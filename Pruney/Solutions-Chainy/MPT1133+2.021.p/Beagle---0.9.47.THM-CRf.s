%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:14 EST 2020

% Result     : Theorem 21.58s
% Output     : CNFRefutation 23.01s
% Verified   : 
% Statistics : Number of formulae       : 1550 (147580 expanded)
%              Number of leaves         :   50 (47490 expanded)
%              Depth                    :   32
%              Number of atoms          : 4644 (478016 expanded)
%              Number of equality atoms :  449 (74876 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_266,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_170,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_166,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_178,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_207,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_236,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_160,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_143,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( k1_relset_1(A,B,C) = A
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_94,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_92,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_56949,plain,(
    ! [A_8306] :
      ( m1_subset_1(u1_pre_topc(A_8306),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8306))))
      | ~ l1_pre_topc(A_8306) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_60,plain,(
    ! [A_43,B_44] :
      ( l1_pre_topc(g1_pre_topc(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56959,plain,(
    ! [A_8306] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_8306),u1_pre_topc(A_8306)))
      | ~ l1_pre_topc(A_8306) ) ),
    inference(resolution,[status(thm)],[c_56949,c_60])).

tff(c_78,plain,(
    '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_100,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_110,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_100])).

tff(c_40401,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_98,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_96,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_111,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_86])).

tff(c_40532,plain,(
    ! [C_3848,B_3849,A_3850] :
      ( v1_xboole_0(C_3848)
      | ~ m1_subset_1(C_3848,k1_zfmisc_1(k2_zfmisc_1(B_3849,A_3850)))
      | ~ v1_xboole_0(A_3850) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40554,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_111,c_40532])).

tff(c_40561,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_40554])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_201,plain,(
    ! [C_104,A_105,B_106] :
      ( v1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_220,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80,c_201])).

tff(c_40504,plain,(
    ! [C_3844,A_3845,B_3846] :
      ( v4_relat_1(C_3844,A_3845)
      | ~ m1_subset_1(C_3844,k1_zfmisc_1(k2_zfmisc_1(A_3845,B_3846))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_40526,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_111,c_40504])).

tff(c_40646,plain,(
    ! [B_3878,A_3879] :
      ( k1_relat_1(B_3878) = A_3879
      | ~ v1_partfun1(B_3878,A_3879)
      | ~ v4_relat_1(B_3878,A_3879)
      | ~ v1_relat_1(B_3878) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_40658,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40526,c_40646])).

tff(c_40669,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_40658])).

tff(c_40695,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_40669])).

tff(c_88,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_107,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_88])).

tff(c_41054,plain,(
    ! [C_3940,A_3941,B_3942] :
      ( v1_partfun1(C_3940,A_3941)
      | ~ v1_funct_2(C_3940,A_3941,B_3942)
      | ~ v1_funct_1(C_3940)
      | ~ m1_subset_1(C_3940,k1_zfmisc_1(k2_zfmisc_1(A_3941,B_3942)))
      | v1_xboole_0(B_3942) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_41060,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_111,c_41054])).

tff(c_41081,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_41060])).

tff(c_41083,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40561,c_40695,c_41081])).

tff(c_41084,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40669])).

tff(c_41094,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41084,c_107])).

tff(c_41093,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41084,c_111])).

tff(c_40553,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_80,c_40532])).

tff(c_40565,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_40553])).

tff(c_82,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_41095,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41084,c_82])).

tff(c_41092,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41084,c_80])).

tff(c_41306,plain,(
    ! [C_3959,A_3960,B_3961] :
      ( v1_partfun1(C_3959,A_3960)
      | ~ v1_funct_2(C_3959,A_3960,B_3961)
      | ~ v1_funct_1(C_3959)
      | ~ m1_subset_1(C_3959,k1_zfmisc_1(k2_zfmisc_1(A_3960,B_3961)))
      | v1_xboole_0(B_3961) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_41312,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_41092,c_41306])).

tff(c_41333,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_41095,c_41312])).

tff(c_41334,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_40565,c_41333])).

tff(c_40525,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_80,c_40504])).

tff(c_40655,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40525,c_40646])).

tff(c_40666,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_40655])).

tff(c_41692,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41334,c_41084,c_41084,c_40666])).

tff(c_41700,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41692,c_41095])).

tff(c_40423,plain,(
    ! [A_3829] :
      ( m1_subset_1(u1_pre_topc(A_3829),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3829))))
      | ~ l1_pre_topc(A_3829) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40433,plain,(
    ! [A_3829] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_3829),u1_pre_topc(A_3829)))
      | ~ l1_pre_topc(A_3829) ) ),
    inference(resolution,[status(thm)],[c_40423,c_60])).

tff(c_66,plain,(
    ! [A_46] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_46),u1_pre_topc(A_46)))
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_41699,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41692,c_41092])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_3','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_108,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_106])).

tff(c_40451,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_108])).

tff(c_41091,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41084,c_40451])).

tff(c_41629,plain,(
    ! [D_4008,A_4009,B_4010] :
      ( v5_pre_topc(D_4008,A_4009,B_4010)
      | ~ v5_pre_topc(D_4008,g1_pre_topc(u1_struct_0(A_4009),u1_pre_topc(A_4009)),B_4010)
      | ~ m1_subset_1(D_4008,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4009),u1_pre_topc(A_4009))),u1_struct_0(B_4010))))
      | ~ v1_funct_2(D_4008,u1_struct_0(g1_pre_topc(u1_struct_0(A_4009),u1_pre_topc(A_4009))),u1_struct_0(B_4010))
      | ~ m1_subset_1(D_4008,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4009),u1_struct_0(B_4010))))
      | ~ v1_funct_2(D_4008,u1_struct_0(A_4009),u1_struct_0(B_4010))
      | ~ v1_funct_1(D_4008)
      | ~ l1_pre_topc(B_4010)
      | ~ v2_pre_topc(B_4010)
      | ~ l1_pre_topc(A_4009)
      | ~ v2_pre_topc(A_4009) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_41632,plain,(
    ! [D_4008,B_4010] :
      ( v5_pre_topc(D_4008,'#skF_1',B_4010)
      | ~ v5_pre_topc(D_4008,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_4010)
      | ~ m1_subset_1(D_4008,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_4010))))
      | ~ v1_funct_2(D_4008,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_4010))
      | ~ m1_subset_1(D_4008,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_4010))))
      | ~ v1_funct_2(D_4008,u1_struct_0('#skF_1'),u1_struct_0(B_4010))
      | ~ v1_funct_1(D_4008)
      | ~ l1_pre_topc(B_4010)
      | ~ v2_pre_topc(B_4010)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41084,c_41629])).

tff(c_41645,plain,(
    ! [D_4008,B_4010] :
      ( v5_pre_topc(D_4008,'#skF_1',B_4010)
      | ~ v5_pre_topc(D_4008,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_4010)
      | ~ m1_subset_1(D_4008,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_4010))))
      | ~ v1_funct_2(D_4008,u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_4010))
      | ~ m1_subset_1(D_4008,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_4010))))
      | ~ v1_funct_2(D_4008,k1_relat_1('#skF_4'),u1_struct_0(B_4010))
      | ~ v1_funct_1(D_4008)
      | ~ l1_pre_topc(B_4010)
      | ~ v2_pre_topc(B_4010) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_41084,c_41084,c_41084,c_41084,c_41632])).

tff(c_43965,plain,(
    ! [D_4205,B_4206] :
      ( v5_pre_topc(D_4205,'#skF_1',B_4206)
      | ~ v5_pre_topc(D_4205,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_4206)
      | ~ m1_subset_1(D_4205,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_4206))))
      | ~ v1_funct_2(D_4205,k1_relat_1('#skF_4'),u1_struct_0(B_4206))
      | ~ m1_subset_1(D_4205,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_4206))))
      | ~ v1_funct_2(D_4205,k1_relat_1('#skF_4'),u1_struct_0(B_4206))
      | ~ v1_funct_1(D_4205)
      | ~ l1_pre_topc(B_4206)
      | ~ v2_pre_topc(B_4206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41692,c_41692,c_41645])).

tff(c_43967,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_41699,c_43965])).

tff(c_43982,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_41700,c_41699,c_41091,c_43967])).

tff(c_44023,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_43982])).

tff(c_44026,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_44023])).

tff(c_44030,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_44026])).

tff(c_44031,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_43982])).

tff(c_44033,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_44031])).

tff(c_44036,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40433,c_44033])).

tff(c_44040,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_44036])).

tff(c_44041,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_44031])).

tff(c_43093,plain,(
    ! [D_4114,A_4115,B_4116] :
      ( v5_pre_topc(D_4114,A_4115,B_4116)
      | ~ v5_pre_topc(D_4114,A_4115,g1_pre_topc(u1_struct_0(B_4116),u1_pre_topc(B_4116)))
      | ~ m1_subset_1(D_4114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4115),u1_struct_0(g1_pre_topc(u1_struct_0(B_4116),u1_pre_topc(B_4116))))))
      | ~ v1_funct_2(D_4114,u1_struct_0(A_4115),u1_struct_0(g1_pre_topc(u1_struct_0(B_4116),u1_pre_topc(B_4116))))
      | ~ m1_subset_1(D_4114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4115),u1_struct_0(B_4116))))
      | ~ v1_funct_2(D_4114,u1_struct_0(A_4115),u1_struct_0(B_4116))
      | ~ v1_funct_1(D_4114)
      | ~ l1_pre_topc(B_4116)
      | ~ v2_pre_topc(B_4116)
      | ~ l1_pre_topc(A_4115)
      | ~ v2_pre_topc(A_4115) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_43102,plain,(
    ! [D_4114,B_4116] :
      ( v5_pre_topc(D_4114,'#skF_1',B_4116)
      | ~ v5_pre_topc(D_4114,'#skF_1',g1_pre_topc(u1_struct_0(B_4116),u1_pre_topc(B_4116)))
      | ~ m1_subset_1(D_4114,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4116),u1_pre_topc(B_4116))))))
      | ~ v1_funct_2(D_4114,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4116),u1_pre_topc(B_4116))))
      | ~ m1_subset_1(D_4114,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_4116))))
      | ~ v1_funct_2(D_4114,u1_struct_0('#skF_1'),u1_struct_0(B_4116))
      | ~ v1_funct_1(D_4114)
      | ~ l1_pre_topc(B_4116)
      | ~ v2_pre_topc(B_4116)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41084,c_43093])).

tff(c_44054,plain,(
    ! [D_4210,B_4211] :
      ( v5_pre_topc(D_4210,'#skF_1',B_4211)
      | ~ v5_pre_topc(D_4210,'#skF_1',g1_pre_topc(u1_struct_0(B_4211),u1_pre_topc(B_4211)))
      | ~ m1_subset_1(D_4210,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4211),u1_pre_topc(B_4211))))))
      | ~ v1_funct_2(D_4210,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4211),u1_pre_topc(B_4211))))
      | ~ m1_subset_1(D_4210,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_4211))))
      | ~ v1_funct_2(D_4210,k1_relat_1('#skF_4'),u1_struct_0(B_4211))
      | ~ v1_funct_1(D_4210)
      | ~ l1_pre_topc(B_4211)
      | ~ v2_pre_topc(B_4211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_41084,c_41084,c_41084,c_43102])).

tff(c_44060,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_41699,c_44054])).

tff(c_44079,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_41094,c_41093,c_41700,c_44041,c_44060])).

tff(c_44081,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_44079])).

tff(c_44082,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40553])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_141,plain,(
    ! [B_91,A_92] :
      ( ~ v1_xboole_0(B_91)
      | B_91 = A_92
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_144,plain,(
    ! [A_92] :
      ( k1_xboole_0 = A_92
      | ~ v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_2,c_141])).

tff(c_44094,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44082,c_144])).

tff(c_19022,plain,(
    ! [A_1832] :
      ( m1_subset_1(u1_pre_topc(A_1832),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1832))))
      | ~ l1_pre_topc(A_1832) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_19036,plain,(
    ! [A_1832] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1832),u1_pre_topc(A_1832)))
      | ~ l1_pre_topc(A_1832) ) ),
    inference(resolution,[status(thm)],[c_19022,c_60])).

tff(c_19039,plain,(
    ! [C_1833,A_1834,B_1835] :
      ( v4_relat_1(C_1833,A_1834)
      | ~ m1_subset_1(C_1833,k1_zfmisc_1(k2_zfmisc_1(A_1834,B_1835))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_19061,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_111,c_19039])).

tff(c_19175,plain,(
    ! [B_1858,A_1859] :
      ( k1_relat_1(B_1858) = A_1859
      | ~ v1_partfun1(B_1858,A_1859)
      | ~ v4_relat_1(B_1858,A_1859)
      | ~ v1_relat_1(B_1858) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_19181,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19061,c_19175])).

tff(c_19190,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_19181])).

tff(c_19200,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_19190])).

tff(c_19313,plain,(
    ! [B_1894,C_1895,A_1896] :
      ( k1_xboole_0 = B_1894
      | v1_partfun1(C_1895,A_1896)
      | ~ v1_funct_2(C_1895,A_1896,B_1894)
      | ~ m1_subset_1(C_1895,k1_zfmisc_1(k2_zfmisc_1(A_1896,B_1894)))
      | ~ v1_funct_1(C_1895) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_19319,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_19313])).

tff(c_19340,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_19319])).

tff(c_19341,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_19200,c_19340])).

tff(c_19100,plain,(
    ! [C_1846,B_1847,A_1848] :
      ( v1_xboole_0(C_1846)
      | ~ m1_subset_1(C_1846,k1_zfmisc_1(k2_zfmisc_1(B_1847,A_1848)))
      | ~ v1_xboole_0(A_1848) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_19122,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_111,c_19100])).

tff(c_19128,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_19122])).

tff(c_19351,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19341,c_19128])).

tff(c_19363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_19351])).

tff(c_19364,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_19190])).

tff(c_243,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_8,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_388,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_323,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_345,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_111,c_323])).

tff(c_440,plain,(
    ! [B_145,A_146] :
      ( k1_relat_1(B_145) = A_146
      | ~ v1_partfun1(B_145,A_146)
      | ~ v4_relat_1(B_145,A_146)
      | ~ v1_relat_1(B_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_446,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_345,c_440])).

tff(c_455,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_446])).

tff(c_479,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_640,plain,(
    ! [B_190,C_191,A_192] :
      ( k1_xboole_0 = B_190
      | v1_partfun1(C_191,A_192)
      | ~ v1_funct_2(C_191,A_192,B_190)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_190)))
      | ~ v1_funct_1(C_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_646,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_640])).

tff(c_666,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_646])).

tff(c_667,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_479,c_666])).

tff(c_412,plain,(
    ! [C_142,B_143,A_144] :
      ( v1_xboole_0(C_142)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(B_143,A_144)))
      | ~ v1_xboole_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_434,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_111,c_412])).

tff(c_459,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_677,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_459])).

tff(c_688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_677])).

tff(c_689,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_696,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_107])).

tff(c_695,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_111])).

tff(c_697,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_82])).

tff(c_694,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_80])).

tff(c_935,plain,(
    ! [B_213,C_214,A_215] :
      ( k1_xboole_0 = B_213
      | v1_partfun1(C_214,A_215)
      | ~ v1_funct_2(C_214,A_215,B_213)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_213)))
      | ~ v1_funct_1(C_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_938,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_694,c_935])).

tff(c_958,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_697,c_938])).

tff(c_1061,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_344,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_80,c_323])).

tff(c_443,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_344,c_440])).

tff(c_452,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_443])).

tff(c_1063,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_689,c_689,c_452])).

tff(c_1069,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_697])).

tff(c_293,plain,(
    ! [A_119] :
      ( m1_subset_1(u1_pre_topc(A_119),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119))))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_303,plain,(
    ! [A_119] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_119),u1_pre_topc(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_293,c_60])).

tff(c_829,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_243])).

tff(c_1067,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_694])).

tff(c_2058,plain,(
    ! [D_298,A_299,B_300] :
      ( v5_pre_topc(D_298,A_299,B_300)
      | ~ v5_pre_topc(D_298,g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299)),B_300)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299))),u1_struct_0(B_300))))
      | ~ v1_funct_2(D_298,u1_struct_0(g1_pre_topc(u1_struct_0(A_299),u1_pre_topc(A_299))),u1_struct_0(B_300))
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299),u1_struct_0(B_300))))
      | ~ v1_funct_2(D_298,u1_struct_0(A_299),u1_struct_0(B_300))
      | ~ v1_funct_1(D_298)
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_2067,plain,(
    ! [D_298,B_300] :
      ( v5_pre_topc(D_298,'#skF_1',B_300)
      | ~ v5_pre_topc(D_298,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_300)
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_300))))
      | ~ v1_funct_2(D_298,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_300))
      | ~ m1_subset_1(D_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_300))))
      | ~ v1_funct_2(D_298,u1_struct_0('#skF_1'),u1_struct_0(B_300))
      | ~ v1_funct_1(D_298)
      | ~ l1_pre_topc(B_300)
      | ~ v2_pre_topc(B_300)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_2058])).

tff(c_2579,plain,(
    ! [D_343,B_344] :
      ( v5_pre_topc(D_343,'#skF_1',B_344)
      | ~ v5_pre_topc(D_343,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_344)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_344))))
      | ~ v1_funct_2(D_343,k1_relat_1('#skF_4'),u1_struct_0(B_344))
      | ~ v1_funct_1(D_343)
      | ~ l1_pre_topc(B_344)
      | ~ v2_pre_topc(B_344) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_689,c_689,c_1063,c_689,c_1063,c_689,c_2067])).

tff(c_2582,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1067,c_2579])).

tff(c_2602,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1069,c_829,c_2582])).

tff(c_2641,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2602])).

tff(c_2644,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2641])).

tff(c_2648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_2644])).

tff(c_2649,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2602])).

tff(c_2651,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2649])).

tff(c_2654,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_303,c_2651])).

tff(c_2658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2654])).

tff(c_2659,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2649])).

tff(c_2169,plain,(
    ! [D_308,A_309,B_310] :
      ( v5_pre_topc(D_308,A_309,B_310)
      | ~ v5_pre_topc(D_308,A_309,g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310)))
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_309),u1_struct_0(g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310))))))
      | ~ v1_funct_2(D_308,u1_struct_0(A_309),u1_struct_0(g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310))))
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_309),u1_struct_0(B_310))))
      | ~ v1_funct_2(D_308,u1_struct_0(A_309),u1_struct_0(B_310))
      | ~ v1_funct_1(D_308)
      | ~ l1_pre_topc(B_310)
      | ~ v2_pre_topc(B_310)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_2178,plain,(
    ! [D_308,B_310] :
      ( v5_pre_topc(D_308,'#skF_1',B_310)
      | ~ v5_pre_topc(D_308,'#skF_1',g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310)))
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310))))))
      | ~ v1_funct_2(D_308,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_310),u1_pre_topc(B_310))))
      | ~ m1_subset_1(D_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_310))))
      | ~ v1_funct_2(D_308,u1_struct_0('#skF_1'),u1_struct_0(B_310))
      | ~ v1_funct_1(D_308)
      | ~ l1_pre_topc(B_310)
      | ~ v2_pre_topc(B_310)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_2169])).

tff(c_2801,plain,(
    ! [D_359,B_360] :
      ( v5_pre_topc(D_359,'#skF_1',B_360)
      | ~ v5_pre_topc(D_359,'#skF_1',g1_pre_topc(u1_struct_0(B_360),u1_pre_topc(B_360)))
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_360),u1_pre_topc(B_360))))))
      | ~ v1_funct_2(D_359,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_360),u1_pre_topc(B_360))))
      | ~ m1_subset_1(D_359,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_360))))
      | ~ v1_funct_2(D_359,k1_relat_1('#skF_4'),u1_struct_0(B_360))
      | ~ v1_funct_1(D_359)
      | ~ l1_pre_topc(B_360)
      | ~ v2_pre_topc(B_360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_689,c_689,c_689,c_2178])).

tff(c_2807,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1067,c_2801])).

tff(c_2826,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_696,c_695,c_1069,c_2659,c_2807])).

tff(c_2828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_2826])).

tff(c_2829,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_22,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_198,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(resolution,[status(thm)],[c_80,c_22])).

tff(c_786,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_198])).

tff(c_787,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(splitLeft,[status(thm)],[c_786])).

tff(c_2831,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2829,c_787])).

tff(c_2839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_2831])).

tff(c_2840,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_786])).

tff(c_2847,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2840,c_144])).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2866,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_10])).

tff(c_20,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_741,plain,(
    ! [A_193,B_194,C_195] :
      ( k1_relset_1(A_193,B_194,C_195) = k1_relat_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_757,plain,(
    ! [A_193,B_194] : k1_relset_1(A_193,B_194,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_741])).

tff(c_2849,plain,(
    ! [A_193,B_194] : k1_relset_1(A_193,B_194,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_757])).

tff(c_2865,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_20])).

tff(c_3104,plain,(
    ! [C_379,A_380,B_381] :
      ( v1_funct_2(C_379,A_380,B_381)
      | k1_relset_1(A_380,B_381,C_379) != A_380
      | ~ m1_subset_1(C_379,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381)))
      | ~ v1_funct_1(C_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_3114,plain,(
    ! [A_380,B_381] :
      ( v1_funct_2('#skF_4',A_380,B_381)
      | k1_relset_1(A_380,B_381,'#skF_4') != A_380
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2865,c_3104])).

tff(c_3121,plain,(
    ! [A_380,B_381] :
      ( v1_funct_2('#skF_4',A_380,B_381)
      | k1_relat_1('#skF_4') != A_380 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2849,c_3114])).

tff(c_3885,plain,(
    ! [C_430,A_431,B_432] :
      ( ~ v1_xboole_0(C_430)
      | ~ v1_funct_2(C_430,A_431,B_432)
      | ~ v1_funct_1(C_430)
      | ~ m1_subset_1(C_430,k1_zfmisc_1(k2_zfmisc_1(A_431,B_432)))
      | v1_xboole_0(B_432)
      | v1_xboole_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_3895,plain,(
    ! [A_431,B_432] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_431,B_432)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_432)
      | v1_xboole_0(A_431) ) ),
    inference(resolution,[status(thm)],[c_2865,c_3885])).

tff(c_3920,plain,(
    ! [A_435,B_436] :
      ( ~ v1_funct_2('#skF_4',A_435,B_436)
      | v1_xboole_0(B_436)
      | v1_xboole_0(A_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2840,c_3895])).

tff(c_3924,plain,(
    ! [B_381,A_380] :
      ( v1_xboole_0(B_381)
      | v1_xboole_0(A_380)
      | k1_relat_1('#skF_4') != A_380 ) ),
    inference(resolution,[status(thm)],[c_3121,c_3920])).

tff(c_3927,plain,(
    ! [A_437] :
      ( v1_xboole_0(A_437)
      | k1_relat_1('#skF_4') != A_437 ) ),
    inference(splitLeft,[status(thm)],[c_3924])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( ~ v1_xboole_0(B_2)
      | B_2 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2848,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_2840,c_4])).

tff(c_3987,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3927,c_2848])).

tff(c_3877,plain,(
    ! [A_428,B_429] :
      ( v1_funct_2('#skF_4',A_428,B_429)
      | k1_relat_1('#skF_4') != A_428 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2849,c_3114])).

tff(c_56,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,k1_xboole_0)
      | ~ v1_funct_2(C_42,k1_xboole_0,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_41)))
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_113,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,k1_xboole_0)
      | ~ v1_funct_2(C_42,k1_xboole_0,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_56])).

tff(c_3064,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_2847,c_2847,c_113])).

tff(c_3880,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_3877,c_3064])).

tff(c_3883,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2865,c_3880])).

tff(c_3884,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3883])).

tff(c_4001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3987,c_3884])).

tff(c_4002,plain,(
    ! [B_381] : v1_xboole_0(B_381) ),
    inference(splitRight,[status(thm)],[c_3924])).

tff(c_16,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_230,plain,(
    ! [C_109] :
      ( v1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_201])).

tff(c_239,plain,(
    ! [B_6] :
      ( v1_relat_1(B_6)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16,c_230])).

tff(c_242,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_2860,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2847,c_242])).

tff(c_4035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4002,c_2860])).

tff(c_4037,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3883])).

tff(c_179,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_111,c_22])).

tff(c_244,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_693,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_689,c_244])).

tff(c_4048,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4037,c_693])).

tff(c_4053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_2866,c_4048])).

tff(c_4054,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_4061,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4054,c_144])).

tff(c_4078,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4061,c_4061,c_8])).

tff(c_4055,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_4123,plain,(
    ! [A_446] :
      ( A_446 = '#skF_4'
      | ~ v1_xboole_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_4054,c_4])).

tff(c_4130,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4055,c_4123])).

tff(c_4134,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4130,c_244])).

tff(c_4286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4054,c_4078,c_4134])).

tff(c_4287,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_4472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_4287])).

tff(c_4474,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_4473,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_4481,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4473,c_4])).

tff(c_18482,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4474,c_4481])).

tff(c_4480,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4473,c_144])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18537,plain,(
    ! [B_1756,A_1757] :
      ( B_1756 = '#skF_4'
      | A_1757 = '#skF_4'
      | k2_zfmisc_1(A_1757,B_1756) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_4480,c_4480,c_6])).

tff(c_18547,plain,
    ( u1_struct_0('#skF_2') = '#skF_4'
    | u1_struct_0('#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_18482,c_18537])).

tff(c_18552,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18547])).

tff(c_18672,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18552,c_243])).

tff(c_4482,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_64,plain,(
    ! [A_45] :
      ( m1_subset_1(u1_pre_topc(A_45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45))))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4695,plain,(
    ! [A_505,B_506] :
      ( l1_pre_topc(g1_pre_topc(A_505,B_506))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(k1_zfmisc_1(A_505))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_4711,plain,(
    ! [A_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_4695])).

tff(c_4487,plain,(
    ! [A_92] :
      ( A_92 = '#skF_4'
      | ~ v1_xboole_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_144])).

tff(c_4567,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4474,c_4487])).

tff(c_4634,plain,(
    ! [B_501,A_502] :
      ( B_501 = '#skF_4'
      | A_502 = '#skF_4'
      | k2_zfmisc_1(A_502,B_501) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_4480,c_4480,c_6])).

tff(c_4644,plain,
    ( u1_struct_0('#skF_2') = '#skF_4'
    | u1_struct_0('#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4567,c_4634])).

tff(c_4649,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4644])).

tff(c_4806,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_243])).

tff(c_4841,plain,(
    ! [A_530] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_530),u1_pre_topc(A_530)))
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4844,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_4841])).

tff(c_4846,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_4844])).

tff(c_4658,plain,(
    ! [A_503] :
      ( m1_subset_1(u1_pre_topc(A_503),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_503))))
      | ~ l1_pre_topc(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_4670,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_4658])).

tff(c_4675,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_4670])).

tff(c_4710,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4675,c_4695])).

tff(c_4488,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_20])).

tff(c_4651,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_107])).

tff(c_10828,plain,(
    ! [C_1047,B_1048] :
      ( v1_partfun1(C_1047,'#skF_4')
      | ~ v1_funct_2(C_1047,'#skF_4',B_1048)
      | ~ m1_subset_1(C_1047,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1047) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_4480,c_4480,c_113])).

tff(c_10833,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4651,c_10828])).

tff(c_10839,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_10833])).

tff(c_4714,plain,(
    ! [C_507,A_508,B_509] :
      ( v4_relat_1(C_507,A_508)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(k2_zfmisc_1(A_508,B_509))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4729,plain,(
    ! [A_508] : v4_relat_1('#skF_4',A_508) ),
    inference(resolution,[status(thm)],[c_4488,c_4714])).

tff(c_10709,plain,(
    ! [B_1018,A_1019] :
      ( k1_relat_1(B_1018) = A_1019
      | ~ v1_partfun1(B_1018,A_1019)
      | ~ v4_relat_1(B_1018,A_1019)
      | ~ v1_relat_1(B_1018) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_10712,plain,(
    ! [A_508] :
      ( k1_relat_1('#skF_4') = A_508
      | ~ v1_partfun1('#skF_4',A_508)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4729,c_10709])).

tff(c_10715,plain,(
    ! [A_508] :
      ( k1_relat_1('#skF_4') = A_508
      | ~ v1_partfun1('#skF_4',A_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_10712])).

tff(c_10843,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10839,c_10715])).

tff(c_10730,plain,(
    ! [A_1024,B_1025,C_1026] :
      ( k1_relset_1(A_1024,B_1025,C_1026) = k1_relat_1(C_1026)
      | ~ m1_subset_1(C_1026,k1_zfmisc_1(k2_zfmisc_1(A_1024,B_1025))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10745,plain,(
    ! [A_1024,B_1025] : k1_relset_1(A_1024,B_1025,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4488,c_10730])).

tff(c_10774,plain,(
    ! [C_1033,A_1034,B_1035] :
      ( v1_funct_2(C_1033,A_1034,B_1035)
      | k1_relset_1(A_1034,B_1035,C_1033) != A_1034
      | ~ m1_subset_1(C_1033,k1_zfmisc_1(k2_zfmisc_1(A_1034,B_1035)))
      | ~ v1_funct_1(C_1033) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_10784,plain,(
    ! [A_1034,B_1035] :
      ( v1_funct_2('#skF_4',A_1034,B_1035)
      | k1_relset_1(A_1034,B_1035,'#skF_4') != A_1034
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4488,c_10774])).

tff(c_10791,plain,(
    ! [A_1034,B_1035] :
      ( v1_funct_2('#skF_4',A_1034,B_1035)
      | k1_relat_1('#skF_4') != A_1034 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10745,c_10784])).

tff(c_10893,plain,(
    ! [B_1035] : v1_funct_2('#skF_4','#skF_4',B_1035) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10843,c_10791])).

tff(c_4652,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4649,c_82])).

tff(c_58,plain,(
    ! [B_41,C_42,A_40] :
      ( k1_xboole_0 = B_41
      | v1_partfun1(C_42,A_40)
      | ~ v1_funct_2(C_42,A_40,B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41)))
      | ~ v1_funct_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10913,plain,(
    ! [B_1059,C_1060,A_1061] :
      ( B_1059 = '#skF_4'
      | v1_partfun1(C_1060,A_1061)
      | ~ v1_funct_2(C_1060,A_1061,B_1059)
      | ~ m1_subset_1(C_1060,k1_zfmisc_1(k2_zfmisc_1(A_1061,B_1059)))
      | ~ v1_funct_1(C_1060) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_58])).

tff(c_10923,plain,(
    ! [B_1059,A_1061] :
      ( B_1059 = '#skF_4'
      | v1_partfun1('#skF_4',A_1061)
      | ~ v1_funct_2('#skF_4',A_1061,B_1059)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4488,c_10913])).

tff(c_10940,plain,(
    ! [B_1063,A_1064] :
      ( B_1063 = '#skF_4'
      | v1_partfun1('#skF_4',A_1064)
      | ~ v1_funct_2('#skF_4',A_1064,B_1063) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10923])).

tff(c_10948,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_4652,c_10940])).

tff(c_10953,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_10948])).

tff(c_10846,plain,(
    ! [A_508] :
      ( A_508 = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10843,c_10715])).

tff(c_10957,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_10953,c_10846])).

tff(c_11451,plain,(
    ! [D_1119,A_1120,B_1121] :
      ( v5_pre_topc(D_1119,A_1120,B_1121)
      | ~ v5_pre_topc(D_1119,A_1120,g1_pre_topc(u1_struct_0(B_1121),u1_pre_topc(B_1121)))
      | ~ m1_subset_1(D_1119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1120),u1_struct_0(g1_pre_topc(u1_struct_0(B_1121),u1_pre_topc(B_1121))))))
      | ~ v1_funct_2(D_1119,u1_struct_0(A_1120),u1_struct_0(g1_pre_topc(u1_struct_0(B_1121),u1_pre_topc(B_1121))))
      | ~ m1_subset_1(D_1119,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1120),u1_struct_0(B_1121))))
      | ~ v1_funct_2(D_1119,u1_struct_0(A_1120),u1_struct_0(B_1121))
      | ~ v1_funct_1(D_1119)
      | ~ l1_pre_topc(B_1121)
      | ~ v2_pre_topc(B_1121)
      | ~ l1_pre_topc(A_1120)
      | ~ v2_pre_topc(A_1120) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_11470,plain,(
    ! [A_1120,B_1121] :
      ( v5_pre_topc('#skF_4',A_1120,B_1121)
      | ~ v5_pre_topc('#skF_4',A_1120,g1_pre_topc(u1_struct_0(B_1121),u1_pre_topc(B_1121)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1120),u1_struct_0(g1_pre_topc(u1_struct_0(B_1121),u1_pre_topc(B_1121))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1120),u1_struct_0(B_1121))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1120),u1_struct_0(B_1121))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1121)
      | ~ v2_pre_topc(B_1121)
      | ~ l1_pre_topc(A_1120)
      | ~ v2_pre_topc(A_1120) ) ),
    inference(resolution,[status(thm)],[c_4488,c_11451])).

tff(c_11660,plain,(
    ! [A_1138,B_1139] :
      ( v5_pre_topc('#skF_4',A_1138,B_1139)
      | ~ v5_pre_topc('#skF_4',A_1138,g1_pre_topc(u1_struct_0(B_1139),u1_pre_topc(B_1139)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1138),u1_struct_0(g1_pre_topc(u1_struct_0(B_1139),u1_pre_topc(B_1139))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1138),u1_struct_0(B_1139))
      | ~ l1_pre_topc(B_1139)
      | ~ v2_pre_topc(B_1139)
      | ~ l1_pre_topc(A_1138)
      | ~ v2_pre_topc(A_1138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_11470])).

tff(c_11666,plain,(
    ! [B_1139] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1139)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_1139),u1_pre_topc(B_1139)))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1139),u1_pre_topc(B_1139))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1139))
      | ~ l1_pre_topc(B_1139)
      | ~ v2_pre_topc(B_1139)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10957,c_11660])).

tff(c_11732,plain,(
    ! [B_1142] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1142)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_1142),u1_pre_topc(B_1142)))
      | ~ l1_pre_topc(B_1142)
      | ~ v2_pre_topc(B_1142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4846,c_4710,c_10893,c_10957,c_10893,c_11666])).

tff(c_11748,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4806,c_11732])).

tff(c_11764,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_11748])).

tff(c_11089,plain,(
    ! [D_1078,A_1079,B_1080] :
      ( v5_pre_topc(D_1078,A_1079,B_1080)
      | ~ v5_pre_topc(D_1078,g1_pre_topc(u1_struct_0(A_1079),u1_pre_topc(A_1079)),B_1080)
      | ~ m1_subset_1(D_1078,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1079),u1_pre_topc(A_1079))),u1_struct_0(B_1080))))
      | ~ v1_funct_2(D_1078,u1_struct_0(g1_pre_topc(u1_struct_0(A_1079),u1_pre_topc(A_1079))),u1_struct_0(B_1080))
      | ~ m1_subset_1(D_1078,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1079),u1_struct_0(B_1080))))
      | ~ v1_funct_2(D_1078,u1_struct_0(A_1079),u1_struct_0(B_1080))
      | ~ v1_funct_1(D_1078)
      | ~ l1_pre_topc(B_1080)
      | ~ v2_pre_topc(B_1080)
      | ~ l1_pre_topc(A_1079)
      | ~ v2_pre_topc(A_1079) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_11105,plain,(
    ! [A_1079,B_1080] :
      ( v5_pre_topc('#skF_4',A_1079,B_1080)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1079),u1_pre_topc(A_1079)),B_1080)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1079),u1_pre_topc(A_1079))),u1_struct_0(B_1080))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1079),u1_struct_0(B_1080))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1079),u1_struct_0(B_1080))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1080)
      | ~ v2_pre_topc(B_1080)
      | ~ l1_pre_topc(A_1079)
      | ~ v2_pre_topc(A_1079) ) ),
    inference(resolution,[status(thm)],[c_4488,c_11089])).

tff(c_11768,plain,(
    ! [A_1143,B_1144] :
      ( v5_pre_topc('#skF_4',A_1143,B_1144)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1143),u1_pre_topc(A_1143)),B_1144)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1143),u1_pre_topc(A_1143))),u1_struct_0(B_1144))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1143),u1_struct_0(B_1144))
      | ~ l1_pre_topc(B_1144)
      | ~ v2_pre_topc(B_1144)
      | ~ l1_pre_topc(A_1143)
      | ~ v2_pre_topc(A_1143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_11105])).

tff(c_11783,plain,(
    ! [B_1144] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1144)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1144)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1144))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1144))
      | ~ l1_pre_topc(B_1144)
      | ~ v2_pre_topc(B_1144)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_11768])).

tff(c_11820,plain,(
    ! [B_1146] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1146)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1146)
      | ~ l1_pre_topc(B_1146)
      | ~ v2_pre_topc(B_1146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_10893,c_4649,c_10893,c_10957,c_4649,c_11783])).

tff(c_11823,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_11764,c_11820])).

tff(c_11840,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_11823])).

tff(c_11842,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4482,c_11840])).

tff(c_11843,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_10948])).

tff(c_62,plain,(
    ! [A_43,B_44] :
      ( v1_pre_topc(g1_pre_topc(A_43,B_44))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_4671,plain,(
    ! [A_503] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_503),u1_pre_topc(A_503)))
      | ~ l1_pre_topc(A_503) ) ),
    inference(resolution,[status(thm)],[c_4658,c_62])).

tff(c_11866,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11843,c_4671])).

tff(c_12114,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_11866])).

tff(c_12120,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4711,c_12114])).

tff(c_12125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12120])).

tff(c_12127,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_11866])).

tff(c_11857,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11843,c_66])).

tff(c_12327,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12127,c_11857])).

tff(c_12328,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_12327])).

tff(c_12331,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_12328])).

tff(c_12335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12331])).

tff(c_12337,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_12327])).

tff(c_14,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11869,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11843,c_64])).

tff(c_12202,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12127,c_11869])).

tff(c_24,plain,(
    ! [A_11,C_13,B_12] :
      ( m1_subset_1(A_11,C_13)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(C_13))
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12224,plain,(
    ! [A_1190] :
      ( m1_subset_1(A_1190,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_1190,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ) ),
    inference(resolution,[status(thm)],[c_12202,c_24])).

tff(c_12229,plain,(
    ! [B_6] :
      ( m1_subset_1(B_6,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_6,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ) ),
    inference(resolution,[status(thm)],[c_14,c_12224])).

tff(c_12312,plain,(
    v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_12229])).

tff(c_12324,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12312,c_4487])).

tff(c_12272,plain,(
    ! [D_1199,A_1200,B_1201] :
      ( v5_pre_topc(D_1199,A_1200,g1_pre_topc(u1_struct_0(B_1201),u1_pre_topc(B_1201)))
      | ~ v5_pre_topc(D_1199,A_1200,B_1201)
      | ~ m1_subset_1(D_1199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1200),u1_struct_0(g1_pre_topc(u1_struct_0(B_1201),u1_pre_topc(B_1201))))))
      | ~ v1_funct_2(D_1199,u1_struct_0(A_1200),u1_struct_0(g1_pre_topc(u1_struct_0(B_1201),u1_pre_topc(B_1201))))
      | ~ m1_subset_1(D_1199,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1200),u1_struct_0(B_1201))))
      | ~ v1_funct_2(D_1199,u1_struct_0(A_1200),u1_struct_0(B_1201))
      | ~ v1_funct_1(D_1199)
      | ~ l1_pre_topc(B_1201)
      | ~ v2_pre_topc(B_1201)
      | ~ l1_pre_topc(A_1200)
      | ~ v2_pre_topc(A_1200) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_12291,plain,(
    ! [A_1200,B_1201] :
      ( v5_pre_topc('#skF_4',A_1200,g1_pre_topc(u1_struct_0(B_1201),u1_pre_topc(B_1201)))
      | ~ v5_pre_topc('#skF_4',A_1200,B_1201)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1200),u1_struct_0(g1_pre_topc(u1_struct_0(B_1201),u1_pre_topc(B_1201))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1200),u1_struct_0(B_1201))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1200),u1_struct_0(B_1201))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1201)
      | ~ v2_pre_topc(B_1201)
      | ~ l1_pre_topc(A_1200)
      | ~ v2_pre_topc(A_1200) ) ),
    inference(resolution,[status(thm)],[c_4488,c_12272])).

tff(c_12520,plain,(
    ! [A_1210,B_1211] :
      ( v5_pre_topc('#skF_4',A_1210,g1_pre_topc(u1_struct_0(B_1211),u1_pre_topc(B_1211)))
      | ~ v5_pre_topc('#skF_4',A_1210,B_1211)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1210),u1_struct_0(g1_pre_topc(u1_struct_0(B_1211),u1_pre_topc(B_1211))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1210),u1_struct_0(B_1211))
      | ~ l1_pre_topc(B_1211)
      | ~ v2_pre_topc(B_1211)
      | ~ l1_pre_topc(A_1210)
      | ~ v2_pre_topc(A_1210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_12291])).

tff(c_12538,plain,(
    ! [B_1211] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1211),u1_pre_topc(B_1211)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_1211)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1211),u1_pre_topc(B_1211))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1211))
      | ~ l1_pre_topc(B_1211)
      | ~ v2_pre_topc(B_1211)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_12520])).

tff(c_12556,plain,(
    ! [B_1212] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1212),u1_pre_topc(B_1212)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_1212)
      | ~ l1_pre_topc(B_1212)
      | ~ v2_pre_topc(B_1212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_10893,c_4649,c_10893,c_12538])).

tff(c_12562,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11843,c_12556])).

tff(c_12569,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12337,c_12127,c_12324,c_12562])).

tff(c_12572,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_12569])).

tff(c_11845,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11843,c_4652])).

tff(c_12060,plain,(
    ! [D_1169,A_1170,B_1171] :
      ( v5_pre_topc(D_1169,A_1170,B_1171)
      | ~ v5_pre_topc(D_1169,g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170)),B_1171)
      | ~ m1_subset_1(D_1169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170))),u1_struct_0(B_1171))))
      | ~ v1_funct_2(D_1169,u1_struct_0(g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170))),u1_struct_0(B_1171))
      | ~ m1_subset_1(D_1169,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1170),u1_struct_0(B_1171))))
      | ~ v1_funct_2(D_1169,u1_struct_0(A_1170),u1_struct_0(B_1171))
      | ~ v1_funct_1(D_1169)
      | ~ l1_pre_topc(B_1171)
      | ~ v2_pre_topc(B_1171)
      | ~ l1_pre_topc(A_1170)
      | ~ v2_pre_topc(A_1170) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_12079,plain,(
    ! [A_1170,B_1171] :
      ( v5_pre_topc('#skF_4',A_1170,B_1171)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170)),B_1171)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1170),u1_pre_topc(A_1170))),u1_struct_0(B_1171))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1170),u1_struct_0(B_1171))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1170),u1_struct_0(B_1171))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1171)
      | ~ v2_pre_topc(B_1171)
      | ~ l1_pre_topc(A_1170)
      | ~ v2_pre_topc(A_1170) ) ),
    inference(resolution,[status(thm)],[c_4488,c_12060])).

tff(c_12689,plain,(
    ! [A_1217,B_1218] :
      ( v5_pre_topc('#skF_4',A_1217,B_1218)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1217),u1_pre_topc(A_1217)),B_1218)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1217),u1_pre_topc(A_1217))),u1_struct_0(B_1218))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1217),u1_struct_0(B_1218))
      | ~ l1_pre_topc(B_1218)
      | ~ v2_pre_topc(B_1218)
      | ~ l1_pre_topc(A_1217)
      | ~ v2_pre_topc(A_1217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_12079])).

tff(c_12707,plain,(
    ! [B_1218] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1218)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1218)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1218))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1218))
      | ~ l1_pre_topc(B_1218)
      | ~ v2_pre_topc(B_1218)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_12689])).

tff(c_12733,plain,(
    ! [B_1220] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1220)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_1220)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_1220))
      | ~ l1_pre_topc(B_1220)
      | ~ v2_pre_topc(B_1220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_10893,c_4649,c_4649,c_12707])).

tff(c_12736,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11843,c_12733])).

tff(c_12744,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12337,c_12127,c_11845,c_4806,c_12736])).

tff(c_12746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12572,c_12744])).

tff(c_12748,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_12569])).

tff(c_11968,plain,(
    ! [D_1153,A_1154,B_1155] :
      ( v5_pre_topc(D_1153,A_1154,B_1155)
      | ~ v5_pre_topc(D_1153,A_1154,g1_pre_topc(u1_struct_0(B_1155),u1_pre_topc(B_1155)))
      | ~ m1_subset_1(D_1153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1154),u1_struct_0(g1_pre_topc(u1_struct_0(B_1155),u1_pre_topc(B_1155))))))
      | ~ v1_funct_2(D_1153,u1_struct_0(A_1154),u1_struct_0(g1_pre_topc(u1_struct_0(B_1155),u1_pre_topc(B_1155))))
      | ~ m1_subset_1(D_1153,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1154),u1_struct_0(B_1155))))
      | ~ v1_funct_2(D_1153,u1_struct_0(A_1154),u1_struct_0(B_1155))
      | ~ v1_funct_1(D_1153)
      | ~ l1_pre_topc(B_1155)
      | ~ v2_pre_topc(B_1155)
      | ~ l1_pre_topc(A_1154)
      | ~ v2_pre_topc(A_1154) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_11987,plain,(
    ! [A_1154,B_1155] :
      ( v5_pre_topc('#skF_4',A_1154,B_1155)
      | ~ v5_pre_topc('#skF_4',A_1154,g1_pre_topc(u1_struct_0(B_1155),u1_pre_topc(B_1155)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1154),u1_struct_0(g1_pre_topc(u1_struct_0(B_1155),u1_pre_topc(B_1155))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1154),u1_struct_0(B_1155))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1154),u1_struct_0(B_1155))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1155)
      | ~ v2_pre_topc(B_1155)
      | ~ l1_pre_topc(A_1154)
      | ~ v2_pre_topc(A_1154) ) ),
    inference(resolution,[status(thm)],[c_4488,c_11968])).

tff(c_12751,plain,(
    ! [A_1221,B_1222] :
      ( v5_pre_topc('#skF_4',A_1221,B_1222)
      | ~ v5_pre_topc('#skF_4',A_1221,g1_pre_topc(u1_struct_0(B_1222),u1_pre_topc(B_1222)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1221),u1_struct_0(g1_pre_topc(u1_struct_0(B_1222),u1_pre_topc(B_1222))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1221),u1_struct_0(B_1222))
      | ~ l1_pre_topc(B_1222)
      | ~ v2_pre_topc(B_1222)
      | ~ l1_pre_topc(A_1221)
      | ~ v2_pre_topc(A_1221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_11987])).

tff(c_12769,plain,(
    ! [B_1222] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1222)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1222),u1_pre_topc(B_1222)))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1222),u1_pre_topc(B_1222))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1222))
      | ~ l1_pre_topc(B_1222)
      | ~ v2_pre_topc(B_1222)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4649,c_12751])).

tff(c_12786,plain,(
    ! [B_1223] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1223)
      | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_1223),u1_pre_topc(B_1223)))
      | ~ l1_pre_topc(B_1223)
      | ~ v2_pre_topc(B_1223) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_10893,c_4649,c_10893,c_12769])).

tff(c_12789,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_12748,c_12786])).

tff(c_12804,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12789])).

tff(c_12806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4482,c_12804])).

tff(c_12807,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4644])).

tff(c_12810,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12807,c_107])).

tff(c_15811,plain,(
    ! [A_1513,B_1514,C_1515] :
      ( k1_relset_1(A_1513,B_1514,C_1515) = k1_relat_1(C_1515)
      | ~ m1_subset_1(C_1515,k1_zfmisc_1(k2_zfmisc_1(A_1513,B_1514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_15826,plain,(
    ! [A_1513,B_1514] : k1_relset_1(A_1513,B_1514,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4488,c_15811])).

tff(c_15903,plain,(
    ! [C_1536,A_1537,B_1538] :
      ( v1_funct_2(C_1536,A_1537,B_1538)
      | k1_relset_1(A_1537,B_1538,C_1536) != A_1537
      | ~ m1_subset_1(C_1536,k1_zfmisc_1(k2_zfmisc_1(A_1537,B_1538)))
      | ~ v1_funct_1(C_1536) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_15913,plain,(
    ! [A_1537,B_1538] :
      ( v1_funct_2('#skF_4',A_1537,B_1538)
      | k1_relset_1(A_1537,B_1538,'#skF_4') != A_1537
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4488,c_15903])).

tff(c_15920,plain,(
    ! [A_1537,B_1538] :
      ( v1_funct_2('#skF_4',A_1537,B_1538)
      | k1_relat_1('#skF_4') != A_1537 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_15826,c_15913])).

tff(c_16048,plain,(
    ! [C_1554,A_1555,B_1556] :
      ( ~ v1_xboole_0(C_1554)
      | ~ v1_funct_2(C_1554,A_1555,B_1556)
      | ~ v1_funct_1(C_1554)
      | ~ m1_subset_1(C_1554,k1_zfmisc_1(k2_zfmisc_1(A_1555,B_1556)))
      | v1_xboole_0(B_1556)
      | v1_xboole_0(A_1555) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16058,plain,(
    ! [A_1555,B_1556] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_1555,B_1556)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_1556)
      | v1_xboole_0(A_1555) ) ),
    inference(resolution,[status(thm)],[c_4488,c_16048])).

tff(c_16069,plain,(
    ! [A_1557,B_1558] :
      ( ~ v1_funct_2('#skF_4',A_1557,B_1558)
      | v1_xboole_0(B_1558)
      | v1_xboole_0(A_1557) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4473,c_16058])).

tff(c_16076,plain,(
    ! [B_1538,A_1537] :
      ( v1_xboole_0(B_1538)
      | v1_xboole_0(A_1537)
      | k1_relat_1('#skF_4') != A_1537 ) ),
    inference(resolution,[status(thm)],[c_15920,c_16069])).

tff(c_16081,plain,(
    ! [A_1559] :
      ( v1_xboole_0(A_1559)
      | k1_relat_1('#skF_4') != A_1559 ) ),
    inference(splitLeft,[status(thm)],[c_16076])).

tff(c_16148,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16081,c_4487])).

tff(c_15923,plain,(
    ! [A_1539,B_1540] :
      ( v1_funct_2('#skF_4',A_1539,B_1540)
      | k1_relat_1('#skF_4') != A_1539 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_15826,c_15913])).

tff(c_15891,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_4480,c_4480,c_113])).

tff(c_15926,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_15923,c_15891])).

tff(c_15932,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_15926])).

tff(c_15934,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_15932])).

tff(c_16162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16148,c_15934])).

tff(c_16163,plain,(
    ! [B_1538] : v1_xboole_0(B_1538) ),
    inference(splitRight,[status(thm)],[c_16076])).

tff(c_13080,plain,(
    ! [A_1261,B_1262,C_1263] :
      ( k1_relset_1(A_1261,B_1262,C_1263) = k1_relat_1(C_1263)
      | ~ m1_subset_1(C_1263,k1_zfmisc_1(k2_zfmisc_1(A_1261,B_1262))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_13095,plain,(
    ! [A_1261,B_1262] : k1_relset_1(A_1261,B_1262,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4488,c_13080])).

tff(c_14427,plain,(
    ! [C_1397,A_1398,B_1399] :
      ( v1_funct_2(C_1397,A_1398,B_1399)
      | k1_relset_1(A_1398,B_1399,C_1397) != A_1398
      | ~ m1_subset_1(C_1397,k1_zfmisc_1(k2_zfmisc_1(A_1398,B_1399)))
      | ~ v1_funct_1(C_1397) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14437,plain,(
    ! [A_1398,B_1399] :
      ( v1_funct_2('#skF_4',A_1398,B_1399)
      | k1_relset_1(A_1398,B_1399,'#skF_4') != A_1398
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4488,c_14427])).

tff(c_14444,plain,(
    ! [A_1398,B_1399] :
      ( v1_funct_2('#skF_4',A_1398,B_1399)
      | k1_relat_1('#skF_4') != A_1398 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13095,c_14437])).

tff(c_14599,plain,(
    ! [C_1415,A_1416,B_1417] :
      ( ~ v1_xboole_0(C_1415)
      | ~ v1_funct_2(C_1415,A_1416,B_1417)
      | ~ v1_funct_1(C_1415)
      | ~ m1_subset_1(C_1415,k1_zfmisc_1(k2_zfmisc_1(A_1416,B_1417)))
      | v1_xboole_0(B_1417)
      | v1_xboole_0(A_1416) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_14609,plain,(
    ! [A_1416,B_1417] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_1416,B_1417)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_1417)
      | v1_xboole_0(A_1416) ) ),
    inference(resolution,[status(thm)],[c_4488,c_14599])).

tff(c_14620,plain,(
    ! [A_1418,B_1419] :
      ( ~ v1_funct_2('#skF_4',A_1418,B_1419)
      | v1_xboole_0(B_1419)
      | v1_xboole_0(A_1418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4473,c_14609])).

tff(c_14627,plain,(
    ! [B_1399,A_1398] :
      ( v1_xboole_0(B_1399)
      | v1_xboole_0(A_1398)
      | k1_relat_1('#skF_4') != A_1398 ) ),
    inference(resolution,[status(thm)],[c_14444,c_14620])).

tff(c_14632,plain,(
    ! [A_1420] :
      ( v1_xboole_0(A_1420)
      | k1_relat_1('#skF_4') != A_1420 ) ),
    inference(splitLeft,[status(thm)],[c_14627])).

tff(c_14676,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14632,c_4487])).

tff(c_14447,plain,(
    ! [A_1400,B_1401] :
      ( v1_funct_2('#skF_4',A_1400,B_1401)
      | k1_relat_1('#skF_4') != A_1400 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13095,c_14437])).

tff(c_13163,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_4480,c_4480,c_113])).

tff(c_14453,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_14447,c_13163])).

tff(c_14457,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_14453])).

tff(c_14458,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_14457])).

tff(c_14690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14676,c_14458])).

tff(c_14691,plain,(
    ! [B_1399] : v1_xboole_0(B_1399) ),
    inference(splitRight,[status(thm)],[c_14627])).

tff(c_12847,plain,(
    ! [A_1230] :
      ( m1_subset_1(u1_pre_topc(A_1230),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1230))))
      | ~ l1_pre_topc(A_1230) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_12862,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12807,c_12847])).

tff(c_12868,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_12862])).

tff(c_12987,plain,(
    ! [A_1247,C_1248,B_1249] :
      ( m1_subset_1(A_1247,C_1248)
      | ~ m1_subset_1(B_1249,k1_zfmisc_1(C_1248))
      | ~ r2_hidden(A_1247,B_1249) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_13007,plain,(
    ! [A_1252] :
      ( m1_subset_1(A_1252,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_1252,u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_12868,c_12987])).

tff(c_13012,plain,(
    ! [B_6] :
      ( m1_subset_1(B_6,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_6,u1_pre_topc('#skF_2'))
      | v1_xboole_0(u1_pre_topc('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_14,c_13007])).

tff(c_13034,plain,(
    v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_13012])).

tff(c_13040,plain,(
    u1_pre_topc('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13034,c_4487])).

tff(c_12811,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12807,c_82])).

tff(c_13049,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13040,c_12811])).

tff(c_13185,plain,(
    ! [C_1287,A_1288,B_1289] :
      ( v1_partfun1(C_1287,A_1288)
      | ~ v1_funct_2(C_1287,A_1288,B_1289)
      | ~ v1_funct_1(C_1287)
      | ~ m1_subset_1(C_1287,k1_zfmisc_1(k2_zfmisc_1(A_1288,B_1289)))
      | v1_xboole_0(B_1289) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_13195,plain,(
    ! [A_1288,B_1289] :
      ( v1_partfun1('#skF_4',A_1288)
      | ~ v1_funct_2('#skF_4',A_1288,B_1289)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_1289) ) ),
    inference(resolution,[status(thm)],[c_4488,c_13185])).

tff(c_13205,plain,(
    ! [A_1290,B_1291] :
      ( v1_partfun1('#skF_4',A_1290)
      | ~ v1_funct_2('#skF_4',A_1290,B_1291)
      | v1_xboole_0(B_1291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13195])).

tff(c_13212,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_13049,c_13205])).

tff(c_13215,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_13212])).

tff(c_13221,plain,(
    u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13215,c_4487])).

tff(c_13224,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13221,c_13049])).

tff(c_12934,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12807,c_243])).

tff(c_13045,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13040,c_12934])).

tff(c_12941,plain,(
    ! [A_1241] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_1241),u1_pre_topc(A_1241)))
      | ~ l1_pre_topc(A_1241)
      | ~ v2_pre_topc(A_1241) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_12944,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12807,c_12941])).

tff(c_12946,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12944])).

tff(c_13044,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13040,c_12946])).

tff(c_12818,plain,(
    ! [A_1224,B_1225] :
      ( l1_pre_topc(g1_pre_topc(A_1224,B_1225))
      | ~ m1_subset_1(B_1225,k1_zfmisc_1(k1_zfmisc_1(A_1224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_12827,plain,(
    ! [A_1224] : l1_pre_topc(g1_pre_topc(A_1224,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_4488,c_12818])).

tff(c_4490,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_4480,c_8])).

tff(c_13825,plain,(
    ! [D_1335,A_1336,B_1337] :
      ( v5_pre_topc(D_1335,A_1336,B_1337)
      | ~ v5_pre_topc(D_1335,g1_pre_topc(u1_struct_0(A_1336),u1_pre_topc(A_1336)),B_1337)
      | ~ m1_subset_1(D_1335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1336),u1_pre_topc(A_1336))),u1_struct_0(B_1337))))
      | ~ v1_funct_2(D_1335,u1_struct_0(g1_pre_topc(u1_struct_0(A_1336),u1_pre_topc(A_1336))),u1_struct_0(B_1337))
      | ~ m1_subset_1(D_1335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1336),u1_struct_0(B_1337))))
      | ~ v1_funct_2(D_1335,u1_struct_0(A_1336),u1_struct_0(B_1337))
      | ~ v1_funct_1(D_1335)
      | ~ l1_pre_topc(B_1337)
      | ~ v2_pre_topc(B_1337)
      | ~ l1_pre_topc(A_1336)
      | ~ v2_pre_topc(A_1336) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_13831,plain,(
    ! [D_1335,A_1336] :
      ( v5_pre_topc(D_1335,A_1336,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_1335,g1_pre_topc(u1_struct_0(A_1336),u1_pre_topc(A_1336)),g1_pre_topc('#skF_4','#skF_4'))
      | ~ m1_subset_1(D_1335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1336),u1_pre_topc(A_1336))),'#skF_4')))
      | ~ v1_funct_2(D_1335,u1_struct_0(g1_pre_topc(u1_struct_0(A_1336),u1_pre_topc(A_1336))),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
      | ~ m1_subset_1(D_1335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1336),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))))
      | ~ v1_funct_2(D_1335,u1_struct_0(A_1336),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
      | ~ v1_funct_1(D_1335)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ l1_pre_topc(A_1336)
      | ~ v2_pre_topc(A_1336) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13221,c_13825])).

tff(c_13978,plain,(
    ! [D_1357,A_1358] :
      ( v5_pre_topc(D_1357,A_1358,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_1357,g1_pre_topc(u1_struct_0(A_1358),u1_pre_topc(A_1358)),g1_pre_topc('#skF_4','#skF_4'))
      | ~ v1_funct_2(D_1357,u1_struct_0(g1_pre_topc(u1_struct_0(A_1358),u1_pre_topc(A_1358))),'#skF_4')
      | ~ m1_subset_1(D_1357,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_1357,u1_struct_0(A_1358),'#skF_4')
      | ~ v1_funct_1(D_1357)
      | ~ l1_pre_topc(A_1358)
      | ~ v2_pre_topc(A_1358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13044,c_12827,c_13221,c_4490,c_13221,c_13221,c_4490,c_13831])).

tff(c_13984,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_13045,c_13978])).

tff(c_13995,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_12810,c_4488,c_13224,c_13984])).

tff(c_13938,plain,(
    ! [D_1350,A_1351,B_1352] :
      ( v5_pre_topc(D_1350,A_1351,B_1352)
      | ~ v5_pre_topc(D_1350,A_1351,g1_pre_topc(u1_struct_0(B_1352),u1_pre_topc(B_1352)))
      | ~ m1_subset_1(D_1350,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1351),u1_struct_0(g1_pre_topc(u1_struct_0(B_1352),u1_pre_topc(B_1352))))))
      | ~ v1_funct_2(D_1350,u1_struct_0(A_1351),u1_struct_0(g1_pre_topc(u1_struct_0(B_1352),u1_pre_topc(B_1352))))
      | ~ m1_subset_1(D_1350,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1351),u1_struct_0(B_1352))))
      | ~ v1_funct_2(D_1350,u1_struct_0(A_1351),u1_struct_0(B_1352))
      | ~ v1_funct_1(D_1350)
      | ~ l1_pre_topc(B_1352)
      | ~ v2_pre_topc(B_1352)
      | ~ l1_pre_topc(A_1351)
      | ~ v2_pre_topc(A_1351) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_13957,plain,(
    ! [A_1351,B_1352] :
      ( v5_pre_topc('#skF_4',A_1351,B_1352)
      | ~ v5_pre_topc('#skF_4',A_1351,g1_pre_topc(u1_struct_0(B_1352),u1_pre_topc(B_1352)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1351),u1_struct_0(g1_pre_topc(u1_struct_0(B_1352),u1_pre_topc(B_1352))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1351),u1_struct_0(B_1352))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1351),u1_struct_0(B_1352))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1352)
      | ~ v2_pre_topc(B_1352)
      | ~ l1_pre_topc(A_1351)
      | ~ v2_pre_topc(A_1351) ) ),
    inference(resolution,[status(thm)],[c_4488,c_13938])).

tff(c_14334,plain,(
    ! [A_1392,B_1393] :
      ( v5_pre_topc('#skF_4',A_1392,B_1393)
      | ~ v5_pre_topc('#skF_4',A_1392,g1_pre_topc(u1_struct_0(B_1393),u1_pre_topc(B_1393)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1392),u1_struct_0(g1_pre_topc(u1_struct_0(B_1393),u1_pre_topc(B_1393))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1392),u1_struct_0(B_1393))
      | ~ l1_pre_topc(B_1393)
      | ~ v2_pre_topc(B_1393)
      | ~ l1_pre_topc(A_1392)
      | ~ v2_pre_topc(A_1392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_13957])).

tff(c_14349,plain,(
    ! [A_1392] :
      ( v5_pre_topc('#skF_4',A_1392,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1392,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1392),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),'#skF_4')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1392),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1392)
      | ~ v2_pre_topc(A_1392) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13040,c_14334])).

tff(c_14413,plain,(
    ! [A_1396] :
      ( v5_pre_topc('#skF_4',A_1396,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1396,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1396),'#skF_4')
      | ~ l1_pre_topc(A_1396)
      | ~ v2_pre_topc(A_1396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12807,c_13221,c_12807,c_12807,c_13040,c_14349])).

tff(c_14416,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_13995,c_14413])).

tff(c_14422,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_12810,c_14416])).

tff(c_14424,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4482,c_14422])).

tff(c_14426,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_13212])).

tff(c_14739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14691,c_14426])).

tff(c_14741,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14457])).

tff(c_14799,plain,(
    ! [B_1399] : v1_funct_2('#skF_4','#skF_4',B_1399) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14741,c_14444])).

tff(c_14425,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_13212])).

tff(c_12830,plain,(
    ! [C_1227,A_1228,B_1229] :
      ( v4_relat_1(C_1227,A_1228)
      | ~ m1_subset_1(C_1227,k1_zfmisc_1(k2_zfmisc_1(A_1228,B_1229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12845,plain,(
    ! [A_1228] : v4_relat_1('#skF_4',A_1228) ),
    inference(resolution,[status(thm)],[c_4488,c_12830])).

tff(c_13015,plain,(
    ! [B_1257,A_1258] :
      ( k1_relat_1(B_1257) = A_1258
      | ~ v1_partfun1(B_1257,A_1258)
      | ~ v4_relat_1(B_1257,A_1258)
      | ~ v1_relat_1(B_1257) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_13018,plain,(
    ! [A_1228] :
      ( k1_relat_1('#skF_4') = A_1228
      | ~ v1_partfun1('#skF_4',A_1228)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12845,c_13015])).

tff(c_13021,plain,(
    ! [A_1228] :
      ( k1_relat_1('#skF_4') = A_1228
      | ~ v1_partfun1('#skF_4',A_1228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_13018])).

tff(c_14748,plain,(
    ! [A_1228] :
      ( A_1228 = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_1228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14741,c_13021])).

tff(c_14798,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_14425,c_14748])).

tff(c_15151,plain,(
    ! [D_1472,A_1473,B_1474] :
      ( v5_pre_topc(D_1472,A_1473,B_1474)
      | ~ v5_pre_topc(D_1472,g1_pre_topc(u1_struct_0(A_1473),u1_pre_topc(A_1473)),B_1474)
      | ~ m1_subset_1(D_1472,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1473),u1_pre_topc(A_1473))),u1_struct_0(B_1474))))
      | ~ v1_funct_2(D_1472,u1_struct_0(g1_pre_topc(u1_struct_0(A_1473),u1_pre_topc(A_1473))),u1_struct_0(B_1474))
      | ~ m1_subset_1(D_1472,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1473),u1_struct_0(B_1474))))
      | ~ v1_funct_2(D_1472,u1_struct_0(A_1473),u1_struct_0(B_1474))
      | ~ v1_funct_1(D_1472)
      | ~ l1_pre_topc(B_1474)
      | ~ v2_pre_topc(B_1474)
      | ~ l1_pre_topc(A_1473)
      | ~ v2_pre_topc(A_1473) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_15173,plain,(
    ! [A_1473,B_1474] :
      ( v5_pre_topc('#skF_4',A_1473,B_1474)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1473),u1_pre_topc(A_1473)),B_1474)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1473),u1_pre_topc(A_1473))),u1_struct_0(B_1474))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1473),u1_struct_0(B_1474))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1473),u1_struct_0(B_1474))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1474)
      | ~ v2_pre_topc(B_1474)
      | ~ l1_pre_topc(A_1473)
      | ~ v2_pre_topc(A_1473) ) ),
    inference(resolution,[status(thm)],[c_4488,c_15151])).

tff(c_15463,plain,(
    ! [A_1490,B_1491] :
      ( v5_pre_topc('#skF_4',A_1490,B_1491)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1490),u1_pre_topc(A_1490)),B_1491)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1490),u1_pre_topc(A_1490))),u1_struct_0(B_1491))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1490),u1_struct_0(B_1491))
      | ~ l1_pre_topc(B_1491)
      | ~ v2_pre_topc(B_1491)
      | ~ l1_pre_topc(A_1490)
      | ~ v2_pre_topc(A_1490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_15173])).

tff(c_15487,plain,(
    ! [A_1490] :
      ( v5_pre_topc('#skF_4',A_1490,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1490),u1_pre_topc(A_1490)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1490),u1_pre_topc(A_1490))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1490),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1490)
      | ~ v2_pre_topc(A_1490) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12807,c_15463])).

tff(c_15595,plain,(
    ! [A_1498] :
      ( v5_pre_topc('#skF_4',A_1498,'#skF_2')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1498),u1_pre_topc(A_1498)),'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1498),u1_pre_topc(A_1498))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1498),'#skF_4')
      | ~ l1_pre_topc(A_1498)
      | ~ v2_pre_topc(A_1498) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12807,c_15487])).

tff(c_15604,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14798,c_15595])).

tff(c_15619,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_12810,c_14799,c_15604])).

tff(c_15620,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_4482,c_15619])).

tff(c_12863,plain,(
    ! [A_1230] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1230),u1_pre_topc(A_1230)))
      | ~ l1_pre_topc(A_1230) ) ),
    inference(resolution,[status(thm)],[c_12847,c_60])).

tff(c_12864,plain,(
    ! [A_1230] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_1230),u1_pre_topc(A_1230)))
      | ~ l1_pre_topc(A_1230) ) ),
    inference(resolution,[status(thm)],[c_12847,c_62])).

tff(c_14840,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14798,c_12864])).

tff(c_15020,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_14840])).

tff(c_15023,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12863,c_15020])).

tff(c_15027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_15023])).

tff(c_15029,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_14840])).

tff(c_14846,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14798,c_64])).

tff(c_15195,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15029,c_14846])).

tff(c_15217,plain,(
    ! [A_1475] :
      ( m1_subset_1(A_1475,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_1475,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_15195,c_24])).

tff(c_15222,plain,(
    ! [B_6] :
      ( m1_subset_1(B_6,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_6,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_14,c_15217])).

tff(c_15253,plain,(
    v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_15222])).

tff(c_15265,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_15253,c_4487])).

tff(c_15042,plain,(
    ! [D_1452,A_1453,B_1454] :
      ( v5_pre_topc(D_1452,A_1453,g1_pre_topc(u1_struct_0(B_1454),u1_pre_topc(B_1454)))
      | ~ v5_pre_topc(D_1452,A_1453,B_1454)
      | ~ m1_subset_1(D_1452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1453),u1_struct_0(g1_pre_topc(u1_struct_0(B_1454),u1_pre_topc(B_1454))))))
      | ~ v1_funct_2(D_1452,u1_struct_0(A_1453),u1_struct_0(g1_pre_topc(u1_struct_0(B_1454),u1_pre_topc(B_1454))))
      | ~ m1_subset_1(D_1452,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1453),u1_struct_0(B_1454))))
      | ~ v1_funct_2(D_1452,u1_struct_0(A_1453),u1_struct_0(B_1454))
      | ~ v1_funct_1(D_1452)
      | ~ l1_pre_topc(B_1454)
      | ~ v2_pre_topc(B_1454)
      | ~ l1_pre_topc(A_1453)
      | ~ v2_pre_topc(A_1453) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_15064,plain,(
    ! [A_1453,B_1454] :
      ( v5_pre_topc('#skF_4',A_1453,g1_pre_topc(u1_struct_0(B_1454),u1_pre_topc(B_1454)))
      | ~ v5_pre_topc('#skF_4',A_1453,B_1454)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1453),u1_struct_0(g1_pre_topc(u1_struct_0(B_1454),u1_pre_topc(B_1454))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1453),u1_struct_0(B_1454))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1453),u1_struct_0(B_1454))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1454)
      | ~ v2_pre_topc(B_1454)
      | ~ l1_pre_topc(A_1453)
      | ~ v2_pre_topc(A_1453) ) ),
    inference(resolution,[status(thm)],[c_4488,c_15042])).

tff(c_15626,plain,(
    ! [A_1499,B_1500] :
      ( v5_pre_topc('#skF_4',A_1499,g1_pre_topc(u1_struct_0(B_1500),u1_pre_topc(B_1500)))
      | ~ v5_pre_topc('#skF_4',A_1499,B_1500)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1499),u1_struct_0(g1_pre_topc(u1_struct_0(B_1500),u1_pre_topc(B_1500))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1499),u1_struct_0(B_1500))
      | ~ l1_pre_topc(B_1500)
      | ~ v2_pre_topc(B_1500)
      | ~ l1_pre_topc(A_1499)
      | ~ v2_pre_topc(A_1499) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_15064])).

tff(c_15647,plain,(
    ! [B_1500] :
      ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0(B_1500),u1_pre_topc(B_1500)))
      | ~ v5_pre_topc('#skF_4','#skF_2',B_1500)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1500),u1_pre_topc(B_1500))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_1500))
      | ~ l1_pre_topc(B_1500)
      | ~ v2_pre_topc(B_1500)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12807,c_15626])).

tff(c_15672,plain,(
    ! [B_1501] :
      ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0(B_1501),u1_pre_topc(B_1501)))
      | ~ v5_pre_topc('#skF_4','#skF_2',B_1501)
      | ~ l1_pre_topc(B_1501)
      | ~ v2_pre_topc(B_1501) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_14799,c_12807,c_14799,c_15647])).

tff(c_15678,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14798,c_15672])).

tff(c_15688,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15029,c_15265,c_15678])).

tff(c_15694,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_15688])).

tff(c_15697,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_15694])).

tff(c_15701,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_15697])).

tff(c_15703,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_15688])).

tff(c_15345,plain,(
    ! [D_1481,A_1482,B_1483] :
      ( v5_pre_topc(D_1481,A_1482,B_1483)
      | ~ v5_pre_topc(D_1481,A_1482,g1_pre_topc(u1_struct_0(B_1483),u1_pre_topc(B_1483)))
      | ~ m1_subset_1(D_1481,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1482),u1_struct_0(g1_pre_topc(u1_struct_0(B_1483),u1_pre_topc(B_1483))))))
      | ~ v1_funct_2(D_1481,u1_struct_0(A_1482),u1_struct_0(g1_pre_topc(u1_struct_0(B_1483),u1_pre_topc(B_1483))))
      | ~ m1_subset_1(D_1481,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1482),u1_struct_0(B_1483))))
      | ~ v1_funct_2(D_1481,u1_struct_0(A_1482),u1_struct_0(B_1483))
      | ~ v1_funct_1(D_1481)
      | ~ l1_pre_topc(B_1483)
      | ~ v2_pre_topc(B_1483)
      | ~ l1_pre_topc(A_1482)
      | ~ v2_pre_topc(A_1482) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_15370,plain,(
    ! [A_1482,B_1483] :
      ( v5_pre_topc('#skF_4',A_1482,B_1483)
      | ~ v5_pre_topc('#skF_4',A_1482,g1_pre_topc(u1_struct_0(B_1483),u1_pre_topc(B_1483)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1482),u1_struct_0(g1_pre_topc(u1_struct_0(B_1483),u1_pre_topc(B_1483))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1482),u1_struct_0(B_1483))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1482),u1_struct_0(B_1483))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1483)
      | ~ v2_pre_topc(B_1483)
      | ~ l1_pre_topc(A_1482)
      | ~ v2_pre_topc(A_1482) ) ),
    inference(resolution,[status(thm)],[c_4488,c_15345])).

tff(c_15704,plain,(
    ! [A_1502,B_1503] :
      ( v5_pre_topc('#skF_4',A_1502,B_1503)
      | ~ v5_pre_topc('#skF_4',A_1502,g1_pre_topc(u1_struct_0(B_1503),u1_pre_topc(B_1503)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1502),u1_struct_0(g1_pre_topc(u1_struct_0(B_1503),u1_pre_topc(B_1503))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1502),u1_struct_0(B_1503))
      | ~ l1_pre_topc(B_1503)
      | ~ v2_pre_topc(B_1503)
      | ~ l1_pre_topc(A_1502)
      | ~ v2_pre_topc(A_1502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_15370])).

tff(c_15710,plain,(
    ! [B_1503] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1503)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_1503),u1_pre_topc(B_1503)))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_1503),u1_pre_topc(B_1503))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_1503))
      | ~ l1_pre_topc(B_1503)
      | ~ v2_pre_topc(B_1503)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14798,c_15704])).

tff(c_15751,plain,(
    ! [B_1504] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1504)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_1504),u1_pre_topc(B_1504)))
      | ~ l1_pre_topc(B_1504)
      | ~ v2_pre_topc(B_1504) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15703,c_15029,c_14799,c_14798,c_14799,c_15710])).

tff(c_15763,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_13040,c_15751])).

tff(c_15773,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_13045,c_12807,c_15763])).

tff(c_15775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15620,c_15773])).

tff(c_15777,plain,(
    ~ v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_13012])).

tff(c_16210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16163,c_15777])).

tff(c_16212,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15932])).

tff(c_16237,plain,(
    ! [A_1537,B_1538] :
      ( v1_funct_2('#skF_4',A_1537,B_1538)
      | A_1537 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16212,c_15920])).

tff(c_16287,plain,(
    ! [C_1569,A_1570,B_1571] :
      ( ~ v1_xboole_0(C_1569)
      | ~ v1_funct_2(C_1569,A_1570,B_1571)
      | ~ v1_funct_1(C_1569)
      | ~ m1_subset_1(C_1569,k1_zfmisc_1(k2_zfmisc_1(A_1570,B_1571)))
      | v1_xboole_0(B_1571)
      | v1_xboole_0(A_1570) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16297,plain,(
    ! [A_1570,B_1571] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_1570,B_1571)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_1571)
      | v1_xboole_0(A_1570) ) ),
    inference(resolution,[status(thm)],[c_4488,c_16287])).

tff(c_16308,plain,(
    ! [A_1572,B_1573] :
      ( ~ v1_funct_2('#skF_4',A_1572,B_1573)
      | v1_xboole_0(B_1573)
      | v1_xboole_0(A_1572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4473,c_16297])).

tff(c_16318,plain,(
    ! [B_1538,A_1537] :
      ( v1_xboole_0(B_1538)
      | v1_xboole_0(A_1537)
      | A_1537 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_16237,c_16308])).

tff(c_16322,plain,(
    ! [A_1537] :
      ( v1_xboole_0(A_1537)
      | A_1537 != '#skF_4' ) ),
    inference(splitLeft,[status(thm)],[c_16318])).

tff(c_16321,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_12811,c_16308])).

tff(c_16369,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_16321])).

tff(c_16416,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16369,c_4487])).

tff(c_16451,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16416,c_12863])).

tff(c_16550,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_16451])).

tff(c_16556,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12863,c_16550])).

tff(c_16561,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_16556])).

tff(c_16563,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16451])).

tff(c_16454,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16416,c_64])).

tff(c_16650,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16563,c_16454])).

tff(c_16672,plain,(
    ! [A_1612] :
      ( m1_subset_1(A_1612,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_1612,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_16650,c_24])).

tff(c_16677,plain,(
    ! [B_6] :
      ( m1_subset_1(B_6,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_6,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
      | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ) ),
    inference(resolution,[status(thm)],[c_14,c_16672])).

tff(c_16760,plain,(
    v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_16677])).

tff(c_16772,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16760,c_4487])).

tff(c_16442,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16416,c_66])).

tff(c_16907,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16563,c_16772,c_16442])).

tff(c_16908,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_16907])).

tff(c_16911,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_16908])).

tff(c_16915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_16911])).

tff(c_16917,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16907])).

tff(c_16818,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16772,c_66])).

tff(c_16853,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16563,c_16416,c_16818])).

tff(c_16905,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_16853])).

tff(c_16919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16917,c_16905])).

tff(c_16921,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16853])).

tff(c_16266,plain,(
    ! [B_1538] : v1_funct_2('#skF_4','#skF_4',B_1538) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16212,c_15920])).

tff(c_16576,plain,(
    ! [D_1600,A_1601,B_1602] :
      ( v5_pre_topc(D_1600,A_1601,B_1602)
      | ~ v5_pre_topc(D_1600,A_1601,g1_pre_topc(u1_struct_0(B_1602),u1_pre_topc(B_1602)))
      | ~ m1_subset_1(D_1600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1601),u1_struct_0(g1_pre_topc(u1_struct_0(B_1602),u1_pre_topc(B_1602))))))
      | ~ v1_funct_2(D_1600,u1_struct_0(A_1601),u1_struct_0(g1_pre_topc(u1_struct_0(B_1602),u1_pre_topc(B_1602))))
      | ~ m1_subset_1(D_1600,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1601),u1_struct_0(B_1602))))
      | ~ v1_funct_2(D_1600,u1_struct_0(A_1601),u1_struct_0(B_1602))
      | ~ v1_funct_1(D_1600)
      | ~ l1_pre_topc(B_1602)
      | ~ v2_pre_topc(B_1602)
      | ~ l1_pre_topc(A_1601)
      | ~ v2_pre_topc(A_1601) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_16595,plain,(
    ! [A_1601,B_1602] :
      ( v5_pre_topc('#skF_4',A_1601,B_1602)
      | ~ v5_pre_topc('#skF_4',A_1601,g1_pre_topc(u1_struct_0(B_1602),u1_pre_topc(B_1602)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1601),u1_struct_0(g1_pre_topc(u1_struct_0(B_1602),u1_pre_topc(B_1602))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1601),u1_struct_0(B_1602))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1601),u1_struct_0(B_1602))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1602)
      | ~ v2_pre_topc(B_1602)
      | ~ l1_pre_topc(A_1601)
      | ~ v2_pre_topc(A_1601) ) ),
    inference(resolution,[status(thm)],[c_4488,c_16576])).

tff(c_16868,plain,(
    ! [A_1625,B_1626] :
      ( v5_pre_topc('#skF_4',A_1625,B_1626)
      | ~ v5_pre_topc('#skF_4',A_1625,g1_pre_topc(u1_struct_0(B_1626),u1_pre_topc(B_1626)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1625),u1_struct_0(g1_pre_topc(u1_struct_0(B_1626),u1_pre_topc(B_1626))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1625),u1_struct_0(B_1626))
      | ~ l1_pre_topc(B_1626)
      | ~ v2_pre_topc(B_1626)
      | ~ l1_pre_topc(A_1625)
      | ~ v2_pre_topc(A_1625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_16595])).

tff(c_16889,plain,(
    ! [A_1625] :
      ( v5_pre_topc('#skF_4',A_1625,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1625,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1625),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1625),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1625)
      | ~ v2_pre_topc(A_1625) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12807,c_16868])).

tff(c_17218,plain,(
    ! [A_1649] :
      ( v5_pre_topc('#skF_4',A_1649,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1649,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1649),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1649),'#skF_4')
      | ~ l1_pre_topc(A_1649)
      | ~ v2_pre_topc(A_1649) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12807,c_12807,c_16889])).

tff(c_17221,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16416,c_17218])).

tff(c_17229,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16921,c_16563,c_16266,c_16416,c_16266,c_12934,c_17221])).

tff(c_16502,plain,(
    ! [D_1588,A_1589,B_1590] :
      ( v5_pre_topc(D_1588,A_1589,B_1590)
      | ~ v5_pre_topc(D_1588,g1_pre_topc(u1_struct_0(A_1589),u1_pre_topc(A_1589)),B_1590)
      | ~ m1_subset_1(D_1588,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1589),u1_pre_topc(A_1589))),u1_struct_0(B_1590))))
      | ~ v1_funct_2(D_1588,u1_struct_0(g1_pre_topc(u1_struct_0(A_1589),u1_pre_topc(A_1589))),u1_struct_0(B_1590))
      | ~ m1_subset_1(D_1588,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1589),u1_struct_0(B_1590))))
      | ~ v1_funct_2(D_1588,u1_struct_0(A_1589),u1_struct_0(B_1590))
      | ~ v1_funct_1(D_1588)
      | ~ l1_pre_topc(B_1590)
      | ~ v2_pre_topc(B_1590)
      | ~ l1_pre_topc(A_1589)
      | ~ v2_pre_topc(A_1589) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_16521,plain,(
    ! [A_1589,B_1590] :
      ( v5_pre_topc('#skF_4',A_1589,B_1590)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1589),u1_pre_topc(A_1589)),B_1590)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1589),u1_pre_topc(A_1589))),u1_struct_0(B_1590))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1589),u1_struct_0(B_1590))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1589),u1_struct_0(B_1590))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1590)
      | ~ v2_pre_topc(B_1590)
      | ~ l1_pre_topc(A_1589)
      | ~ v2_pre_topc(A_1589) ) ),
    inference(resolution,[status(thm)],[c_4488,c_16502])).

tff(c_17076,plain,(
    ! [A_1637,B_1638] :
      ( v5_pre_topc('#skF_4',A_1637,B_1638)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1637),u1_pre_topc(A_1637)),B_1638)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1637),u1_pre_topc(A_1637))),u1_struct_0(B_1638))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1637),u1_struct_0(B_1638))
      | ~ l1_pre_topc(B_1638)
      | ~ v2_pre_topc(B_1638)
      | ~ l1_pre_topc(A_1637)
      | ~ v2_pre_topc(A_1637) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_16521])).

tff(c_17085,plain,(
    ! [B_1638] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1638)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1638)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_1638))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1638))
      | ~ l1_pre_topc(B_1638)
      | ~ v2_pre_topc(B_1638)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16416,c_17076])).

tff(c_17103,plain,(
    ! [B_1638] :
      ( v5_pre_topc('#skF_4','#skF_1',B_1638)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_1638)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_1638))
      | ~ l1_pre_topc(B_1638)
      | ~ v2_pre_topc(B_1638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_16266,c_17085])).

tff(c_17239,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_17229,c_17103])).

tff(c_17245,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12810,c_12807,c_17239])).

tff(c_17247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4482,c_17245])).

tff(c_17249,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_16321])).

tff(c_17356,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_16322,c_17249])).

tff(c_15856,plain,(
    ! [B_1522,C_1523,A_1524] :
      ( B_1522 = '#skF_4'
      | v1_partfun1(C_1523,A_1524)
      | ~ v1_funct_2(C_1523,A_1524,B_1522)
      | ~ m1_subset_1(C_1523,k1_zfmisc_1(k2_zfmisc_1(A_1524,B_1522)))
      | ~ v1_funct_1(C_1523) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4480,c_58])).

tff(c_15866,plain,(
    ! [B_1522,A_1524] :
      ( B_1522 = '#skF_4'
      | v1_partfun1('#skF_4',A_1524)
      | ~ v1_funct_2('#skF_4',A_1524,B_1522)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4488,c_15856])).

tff(c_15876,plain,(
    ! [B_1525,A_1526] :
      ( B_1525 = '#skF_4'
      | v1_partfun1('#skF_4',A_1526)
      | ~ v1_funct_2('#skF_4',A_1526,B_1525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_15866])).

tff(c_15885,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_12811,c_15876])).

tff(c_16258,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_15885])).

tff(c_16239,plain,(
    ! [A_1228] :
      ( A_1228 = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_1228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16212,c_13021])).

tff(c_17359,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_16258,c_16239])).

tff(c_17363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17356,c_17359])).

tff(c_17364,plain,(
    ! [B_1538] : v1_xboole_0(B_1538) ),
    inference(splitRight,[status(thm)],[c_16318])).

tff(c_17410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17364,c_15777])).

tff(c_17411,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15885])).

tff(c_17431,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17411,c_12811])).

tff(c_12882,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_12868,c_60])).

tff(c_17841,plain,(
    ! [D_1712,A_1713,B_1714] :
      ( v5_pre_topc(D_1712,A_1713,B_1714)
      | ~ v5_pre_topc(D_1712,g1_pre_topc(u1_struct_0(A_1713),u1_pre_topc(A_1713)),B_1714)
      | ~ m1_subset_1(D_1712,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1713),u1_pre_topc(A_1713))),u1_struct_0(B_1714))))
      | ~ v1_funct_2(D_1712,u1_struct_0(g1_pre_topc(u1_struct_0(A_1713),u1_pre_topc(A_1713))),u1_struct_0(B_1714))
      | ~ m1_subset_1(D_1712,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1713),u1_struct_0(B_1714))))
      | ~ v1_funct_2(D_1712,u1_struct_0(A_1713),u1_struct_0(B_1714))
      | ~ v1_funct_1(D_1712)
      | ~ l1_pre_topc(B_1714)
      | ~ v2_pre_topc(B_1714)
      | ~ l1_pre_topc(A_1713)
      | ~ v2_pre_topc(A_1713) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_17847,plain,(
    ! [D_1712,A_1713] :
      ( v5_pre_topc(D_1712,A_1713,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1712,g1_pre_topc(u1_struct_0(A_1713),u1_pre_topc(A_1713)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_1712,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1713),u1_pre_topc(A_1713))),'#skF_4')))
      | ~ v1_funct_2(D_1712,u1_struct_0(g1_pre_topc(u1_struct_0(A_1713),u1_pre_topc(A_1713))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_1712,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1713),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_1712,u1_struct_0(A_1713),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_1712)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_1713)
      | ~ v2_pre_topc(A_1713) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17411,c_17841])).

tff(c_17971,plain,(
    ! [D_1715,A_1716] :
      ( v5_pre_topc(D_1715,A_1716,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_1715,g1_pre_topc(u1_struct_0(A_1716),u1_pre_topc(A_1716)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(D_1715,u1_struct_0(g1_pre_topc(u1_struct_0(A_1716),u1_pre_topc(A_1716))),'#skF_4')
      | ~ m1_subset_1(D_1715,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_1715,u1_struct_0(A_1716),'#skF_4')
      | ~ v1_funct_1(D_1715)
      | ~ l1_pre_topc(A_1716)
      | ~ v2_pre_topc(A_1716) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12946,c_12882,c_17411,c_4490,c_17411,c_17411,c_4490,c_17847])).

tff(c_17980,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12934,c_17971])).

tff(c_17990,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_12810,c_4488,c_17431,c_17980])).

tff(c_17576,plain,(
    ! [D_1672,A_1673,B_1674] :
      ( v5_pre_topc(D_1672,A_1673,B_1674)
      | ~ v5_pre_topc(D_1672,A_1673,g1_pre_topc(u1_struct_0(B_1674),u1_pre_topc(B_1674)))
      | ~ m1_subset_1(D_1672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1673),u1_struct_0(g1_pre_topc(u1_struct_0(B_1674),u1_pre_topc(B_1674))))))
      | ~ v1_funct_2(D_1672,u1_struct_0(A_1673),u1_struct_0(g1_pre_topc(u1_struct_0(B_1674),u1_pre_topc(B_1674))))
      | ~ m1_subset_1(D_1672,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1673),u1_struct_0(B_1674))))
      | ~ v1_funct_2(D_1672,u1_struct_0(A_1673),u1_struct_0(B_1674))
      | ~ v1_funct_1(D_1672)
      | ~ l1_pre_topc(B_1674)
      | ~ v2_pre_topc(B_1674)
      | ~ l1_pre_topc(A_1673)
      | ~ v2_pre_topc(A_1673) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_17592,plain,(
    ! [A_1673,B_1674] :
      ( v5_pre_topc('#skF_4',A_1673,B_1674)
      | ~ v5_pre_topc('#skF_4',A_1673,g1_pre_topc(u1_struct_0(B_1674),u1_pre_topc(B_1674)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1673),u1_struct_0(g1_pre_topc(u1_struct_0(B_1674),u1_pre_topc(B_1674))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1673),u1_struct_0(B_1674))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1673),u1_struct_0(B_1674))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1674)
      | ~ v2_pre_topc(B_1674)
      | ~ l1_pre_topc(A_1673)
      | ~ v2_pre_topc(A_1673) ) ),
    inference(resolution,[status(thm)],[c_4488,c_17576])).

tff(c_18291,plain,(
    ! [A_1740,B_1741] :
      ( v5_pre_topc('#skF_4',A_1740,B_1741)
      | ~ v5_pre_topc('#skF_4',A_1740,g1_pre_topc(u1_struct_0(B_1741),u1_pre_topc(B_1741)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1740),u1_struct_0(g1_pre_topc(u1_struct_0(B_1741),u1_pre_topc(B_1741))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1740),u1_struct_0(B_1741))
      | ~ l1_pre_topc(B_1741)
      | ~ v2_pre_topc(B_1741)
      | ~ l1_pre_topc(A_1740)
      | ~ v2_pre_topc(A_1740) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4488,c_17592])).

tff(c_18309,plain,(
    ! [A_1740] :
      ( v5_pre_topc('#skF_4',A_1740,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1740,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1740),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1740),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_1740)
      | ~ v2_pre_topc(A_1740) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12807,c_18291])).

tff(c_18384,plain,(
    ! [A_1744] :
      ( v5_pre_topc('#skF_4',A_1744,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_1744,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1744),'#skF_4')
      | ~ l1_pre_topc(A_1744)
      | ~ v2_pre_topc(A_1744) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_12807,c_17411,c_12807,c_18309])).

tff(c_18394,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_17990,c_18384])).

tff(c_18405,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_12810,c_18394])).

tff(c_18407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4482,c_18405])).

tff(c_18408,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_18744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18672,c_18552,c_18408])).

tff(c_18745,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18547])).

tff(c_18885,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18745,c_243])).

tff(c_18958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18885,c_18745,c_18408])).

tff(c_18960,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_19449,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19364,c_18960])).

tff(c_19121,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_80,c_19100])).

tff(c_19164,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_19121])).

tff(c_19398,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19364,c_82])).

tff(c_19395,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19364,c_80])).

tff(c_19605,plain,(
    ! [C_1911,A_1912,B_1913] :
      ( v1_partfun1(C_1911,A_1912)
      | ~ v1_funct_2(C_1911,A_1912,B_1913)
      | ~ v1_funct_1(C_1911)
      | ~ m1_subset_1(C_1911,k1_zfmisc_1(k2_zfmisc_1(A_1912,B_1913)))
      | v1_xboole_0(B_1913) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_19608,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_19395,c_19605])).

tff(c_19628,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_19398,c_19608])).

tff(c_19629,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_19164,c_19628])).

tff(c_19060,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_80,c_19039])).

tff(c_19178,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_19060,c_19175])).

tff(c_19187,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_19178])).

tff(c_19784,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19629,c_19364,c_19364,c_19187])).

tff(c_19791,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19784,c_19398])).

tff(c_19788,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19784,c_19395])).

tff(c_21034,plain,(
    ! [D_2019,A_2020,B_2021] :
      ( v5_pre_topc(D_2019,g1_pre_topc(u1_struct_0(A_2020),u1_pre_topc(A_2020)),B_2021)
      | ~ v5_pre_topc(D_2019,A_2020,B_2021)
      | ~ m1_subset_1(D_2019,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2020),u1_pre_topc(A_2020))),u1_struct_0(B_2021))))
      | ~ v1_funct_2(D_2019,u1_struct_0(g1_pre_topc(u1_struct_0(A_2020),u1_pre_topc(A_2020))),u1_struct_0(B_2021))
      | ~ m1_subset_1(D_2019,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2020),u1_struct_0(B_2021))))
      | ~ v1_funct_2(D_2019,u1_struct_0(A_2020),u1_struct_0(B_2021))
      | ~ v1_funct_1(D_2019)
      | ~ l1_pre_topc(B_2021)
      | ~ v2_pre_topc(B_2021)
      | ~ l1_pre_topc(A_2020)
      | ~ v2_pre_topc(A_2020) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_21043,plain,(
    ! [D_2019,B_2021] :
      ( v5_pre_topc(D_2019,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2021)
      | ~ v5_pre_topc(D_2019,'#skF_1',B_2021)
      | ~ m1_subset_1(D_2019,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2021))))
      | ~ v1_funct_2(D_2019,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_2021))
      | ~ m1_subset_1(D_2019,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2021))))
      | ~ v1_funct_2(D_2019,u1_struct_0('#skF_1'),u1_struct_0(B_2021))
      | ~ v1_funct_1(D_2019)
      | ~ l1_pre_topc(B_2021)
      | ~ v2_pre_topc(B_2021)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19364,c_21034])).

tff(c_21430,plain,(
    ! [D_2053,B_2054] :
      ( v5_pre_topc(D_2053,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_2054)
      | ~ v5_pre_topc(D_2053,'#skF_1',B_2054)
      | ~ m1_subset_1(D_2053,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_2054))))
      | ~ v1_funct_2(D_2053,k1_relat_1('#skF_4'),u1_struct_0(B_2054))
      | ~ v1_funct_1(D_2053)
      | ~ l1_pre_topc(B_2054)
      | ~ v2_pre_topc(B_2054) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_19364,c_19364,c_19784,c_19364,c_19784,c_19364,c_21043])).

tff(c_21433,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_19788,c_21430])).

tff(c_21453,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_19791,c_21433])).

tff(c_21454,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_19449,c_21453])).

tff(c_21464,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_21454])).

tff(c_21467,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_21464])).

tff(c_21471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_21467])).

tff(c_21472,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_21454])).

tff(c_21474,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_21472])).

tff(c_19397,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19364,c_107])).

tff(c_19396,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19364,c_111])).

tff(c_18959,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_20980,plain,(
    ! [D_2016,A_2017,B_2018] :
      ( v5_pre_topc(D_2016,A_2017,g1_pre_topc(u1_struct_0(B_2018),u1_pre_topc(B_2018)))
      | ~ v5_pre_topc(D_2016,A_2017,B_2018)
      | ~ m1_subset_1(D_2016,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2017),u1_struct_0(g1_pre_topc(u1_struct_0(B_2018),u1_pre_topc(B_2018))))))
      | ~ v1_funct_2(D_2016,u1_struct_0(A_2017),u1_struct_0(g1_pre_topc(u1_struct_0(B_2018),u1_pre_topc(B_2018))))
      | ~ m1_subset_1(D_2016,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2017),u1_struct_0(B_2018))))
      | ~ v1_funct_2(D_2016,u1_struct_0(A_2017),u1_struct_0(B_2018))
      | ~ v1_funct_1(D_2016)
      | ~ l1_pre_topc(B_2018)
      | ~ v2_pre_topc(B_2018)
      | ~ l1_pre_topc(A_2017)
      | ~ v2_pre_topc(A_2017) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_20989,plain,(
    ! [D_2016,B_2018] :
      ( v5_pre_topc(D_2016,'#skF_1',g1_pre_topc(u1_struct_0(B_2018),u1_pre_topc(B_2018)))
      | ~ v5_pre_topc(D_2016,'#skF_1',B_2018)
      | ~ m1_subset_1(D_2016,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_2018),u1_pre_topc(B_2018))))))
      | ~ v1_funct_2(D_2016,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_2018),u1_pre_topc(B_2018))))
      | ~ m1_subset_1(D_2016,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_2018))))
      | ~ v1_funct_2(D_2016,u1_struct_0('#skF_1'),u1_struct_0(B_2018))
      | ~ v1_funct_1(D_2016)
      | ~ l1_pre_topc(B_2018)
      | ~ v2_pre_topc(B_2018)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19364,c_20980])).

tff(c_21616,plain,(
    ! [D_2069,B_2070] :
      ( v5_pre_topc(D_2069,'#skF_1',g1_pre_topc(u1_struct_0(B_2070),u1_pre_topc(B_2070)))
      | ~ v5_pre_topc(D_2069,'#skF_1',B_2070)
      | ~ m1_subset_1(D_2069,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_2070),u1_pre_topc(B_2070))))))
      | ~ v1_funct_2(D_2069,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_2070),u1_pre_topc(B_2070))))
      | ~ m1_subset_1(D_2069,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_2070))))
      | ~ v1_funct_2(D_2069,k1_relat_1('#skF_4'),u1_struct_0(B_2070))
      | ~ v1_funct_1(D_2069)
      | ~ l1_pre_topc(B_2070)
      | ~ v2_pre_topc(B_2070) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_19364,c_19364,c_19364,c_20989])).

tff(c_21622,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_19788,c_21616])).

tff(c_21641,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_19397,c_19396,c_19791,c_18959,c_21622])).

tff(c_21643,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21474,c_21641])).

tff(c_21644,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_21472])).

tff(c_21681,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_19036,c_21644])).

tff(c_21685,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_21681])).

tff(c_21686,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_19121])).

tff(c_21693,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_21686,c_144])).

tff(c_21709,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21693,c_21693,c_10])).

tff(c_21708,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21693,c_20])).

tff(c_21904,plain,(
    ! [A_2091,B_2092,C_2093] :
      ( k1_relset_1(A_2091,B_2092,C_2093) = k1_relat_1(C_2093)
      | ~ m1_subset_1(C_2093,k1_zfmisc_1(k2_zfmisc_1(A_2091,B_2092))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_21919,plain,(
    ! [A_2091,B_2092] : k1_relset_1(A_2091,B_2092,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_21708,c_21904])).

tff(c_22152,plain,(
    ! [C_2125,A_2126,B_2127] :
      ( v1_funct_2(C_2125,A_2126,B_2127)
      | k1_relset_1(A_2126,B_2127,C_2125) != A_2126
      | ~ m1_subset_1(C_2125,k1_zfmisc_1(k2_zfmisc_1(A_2126,B_2127)))
      | ~ v1_funct_1(C_2125) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_22156,plain,(
    ! [A_2126,B_2127] :
      ( v1_funct_2('#skF_4',A_2126,B_2127)
      | k1_relset_1(A_2126,B_2127,'#skF_4') != A_2126
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21708,c_22152])).

tff(c_22173,plain,(
    ! [A_2128,B_2129] :
      ( v1_funct_2('#skF_4',A_2128,B_2129)
      | k1_relat_1('#skF_4') != A_2128 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21919,c_22156])).

tff(c_21988,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21693,c_21693,c_21693,c_113])).

tff(c_22179,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_22173,c_21988])).

tff(c_22183,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21708,c_22179])).

tff(c_22184,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22183])).

tff(c_22169,plain,(
    ! [A_2126,B_2127] :
      ( v1_funct_2('#skF_4',A_2126,B_2127)
      | k1_relat_1('#skF_4') != A_2126 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21919,c_22156])).

tff(c_22244,plain,(
    ! [C_2137,A_2138,B_2139] :
      ( ~ v1_xboole_0(C_2137)
      | ~ v1_funct_2(C_2137,A_2138,B_2139)
      | ~ v1_funct_1(C_2137)
      | ~ m1_subset_1(C_2137,k1_zfmisc_1(k2_zfmisc_1(A_2138,B_2139)))
      | v1_xboole_0(B_2139)
      | v1_xboole_0(A_2138) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_22248,plain,(
    ! [A_2138,B_2139] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_2138,B_2139)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_2139)
      | v1_xboole_0(A_2138) ) ),
    inference(resolution,[status(thm)],[c_21708,c_22244])).

tff(c_22265,plain,(
    ! [A_2140,B_2141] :
      ( ~ v1_funct_2('#skF_4',A_2140,B_2141)
      | v1_xboole_0(B_2141)
      | v1_xboole_0(A_2140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21686,c_22248])).

tff(c_22274,plain,(
    ! [B_2127,A_2126] :
      ( v1_xboole_0(B_2127)
      | v1_xboole_0(A_2126)
      | k1_relat_1('#skF_4') != A_2126 ) ),
    inference(resolution,[status(thm)],[c_22169,c_22265])).

tff(c_22276,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22274])).

tff(c_22040,plain,(
    ! [C_2120,A_2121,B_2122] :
      ( v1_partfun1(C_2120,A_2121)
      | ~ v1_funct_2(C_2120,A_2121,B_2122)
      | ~ v1_funct_1(C_2120)
      | ~ m1_subset_1(C_2120,k1_zfmisc_1(k2_zfmisc_1(A_2121,B_2122)))
      | v1_xboole_0(B_2122) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22044,plain,(
    ! [A_2121,B_2122] :
      ( v1_partfun1('#skF_4',A_2121)
      | ~ v1_funct_2('#skF_4',A_2121,B_2122)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_2122) ) ),
    inference(resolution,[status(thm)],[c_21708,c_22040])).

tff(c_22060,plain,(
    ! [A_2123,B_2124] :
      ( v1_partfun1('#skF_4',A_2123)
      | ~ v1_funct_2('#skF_4',A_2123,B_2124)
      | v1_xboole_0(B_2124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22044])).

tff(c_22066,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_22060])).

tff(c_22071,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_19128,c_22066])).

tff(c_19063,plain,(
    ! [A_1834] : v4_relat_1(k1_xboole_0,A_1834) ),
    inference(resolution,[status(thm)],[c_20,c_19039])).

tff(c_21698,plain,(
    ! [A_1834] : v4_relat_1('#skF_4',A_1834) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21693,c_19063])).

tff(c_21862,plain,(
    ! [B_2085,A_2086] :
      ( k1_relat_1(B_2085) = A_2086
      | ~ v1_partfun1(B_2085,A_2086)
      | ~ v4_relat_1(B_2085,A_2086)
      | ~ v1_relat_1(B_2085) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_21865,plain,(
    ! [A_1834] :
      ( k1_relat_1('#skF_4') = A_1834
      | ~ v1_partfun1('#skF_4',A_1834)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_21698,c_21862])).

tff(c_21868,plain,(
    ! [A_1834] :
      ( k1_relat_1('#skF_4') = A_1834
      | ~ v1_partfun1('#skF_4',A_1834) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_21865])).

tff(c_22075,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22071,c_21868])).

tff(c_19141,plain,(
    ! [A_1850,C_1851,B_1852] :
      ( m1_subset_1(A_1850,C_1851)
      | ~ m1_subset_1(B_1852,k1_zfmisc_1(C_1851))
      | ~ r2_hidden(A_1850,B_1852) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_19153,plain,(
    ! [A_1850,A_45] :
      ( m1_subset_1(A_1850,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ r2_hidden(A_1850,u1_pre_topc(A_45))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_19141])).

tff(c_22087,plain,(
    ! [A_1850] :
      ( m1_subset_1(A_1850,k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ r2_hidden(A_1850,u1_pre_topc('#skF_1'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22075,c_19153])).

tff(c_22231,plain,(
    ! [A_2136] :
      ( m1_subset_1(A_2136,k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ r2_hidden(A_2136,u1_pre_topc('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_22087])).

tff(c_22241,plain,(
    ! [A_2136] :
      ( v1_xboole_0(A_2136)
      | ~ v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ r2_hidden(A_2136,u1_pre_topc('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_22231,c_22])).

tff(c_22243,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_22241])).

tff(c_22279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22276,c_22243])).

tff(c_22280,plain,(
    ! [B_2127] : v1_xboole_0(B_2127) ),
    inference(splitRight,[status(thm)],[c_22274])).

tff(c_22332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22280,c_22243])).

tff(c_22334,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_22241])).

tff(c_21694,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_21686,c_4])).

tff(c_22337,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22334,c_21694])).

tff(c_22343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22184,c_22337])).

tff(c_22345,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22183])).

tff(c_18961,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_22079,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22075,c_18961])).

tff(c_22355,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22345,c_22079])).

tff(c_22362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_21686,c_21709,c_22355])).

tff(c_22363,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_19122])).

tff(c_22370,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22363,c_144])).

tff(c_22402,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22370,c_22370,c_8])).

tff(c_22364,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_19122])).

tff(c_22470,plain,(
    ! [A_2149] :
      ( A_2149 = '#skF_4'
      | ~ v1_xboole_0(A_2149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22370,c_144])).

tff(c_22477,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22364,c_22470])).

tff(c_22490,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22477,c_18961])).

tff(c_22498,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22363,c_22402,c_22490])).

tff(c_22500,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_22499,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_22507,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_22499,c_4])).

tff(c_22593,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22500,c_22507])).

tff(c_22506,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_22499,c_144])).

tff(c_22649,plain,(
    ! [B_2165,A_2166] :
      ( B_2165 = '#skF_4'
      | A_2166 = '#skF_4'
      | k2_zfmisc_1(A_2166,B_2165) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22506,c_22506,c_22506,c_6])).

tff(c_22659,plain,
    ( u1_struct_0('#skF_2') = '#skF_4'
    | u1_struct_0('#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_22593,c_22649])).

tff(c_22664,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_22659])).

tff(c_22830,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22664,c_18960])).

tff(c_22711,plain,(
    ! [A_2169,B_2170] :
      ( l1_pre_topc(g1_pre_topc(A_2169,B_2170))
      | ~ m1_subset_1(B_2170,k1_zfmisc_1(k1_zfmisc_1(A_2169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_22727,plain,(
    ! [A_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_22711])).

tff(c_22668,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22664,c_82])).

tff(c_22513,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22506,c_20])).

tff(c_25702,plain,(
    ! [C_2460,A_2461,B_2462] :
      ( v1_partfun1(C_2460,A_2461)
      | ~ v1_funct_2(C_2460,A_2461,B_2462)
      | ~ v1_funct_1(C_2460)
      | ~ m1_subset_1(C_2460,k1_zfmisc_1(k2_zfmisc_1(A_2461,B_2462)))
      | v1_xboole_0(B_2462) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_25706,plain,(
    ! [A_2461,B_2462] :
      ( v1_partfun1('#skF_4',A_2461)
      | ~ v1_funct_2('#skF_4',A_2461,B_2462)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_2462) ) ),
    inference(resolution,[status(thm)],[c_22513,c_25702])).

tff(c_25722,plain,(
    ! [A_2463,B_2464] :
      ( v1_partfun1('#skF_4',A_2463)
      | ~ v1_funct_2('#skF_4',A_2463,B_2464)
      | v1_xboole_0(B_2464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_25706])).

tff(c_25730,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_22668,c_25722])).

tff(c_25738,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_25730])).

tff(c_25795,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25738,c_22507])).

tff(c_25816,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25795,c_22727])).

tff(c_25961,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_25816])).

tff(c_25964,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22727,c_25961])).

tff(c_25968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_25964])).

tff(c_25970,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_25816])).

tff(c_25810,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25795,c_66])).

tff(c_26457,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25970,c_25810])).

tff(c_26458,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_26457])).

tff(c_26461,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_26458])).

tff(c_26465,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_26461])).

tff(c_26467,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_26457])).

tff(c_22667,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22664,c_107])).

tff(c_25595,plain,(
    ! [C_2441,B_2442] :
      ( v1_partfun1(C_2441,'#skF_4')
      | ~ v1_funct_2(C_2441,'#skF_4',B_2442)
      | ~ m1_subset_1(C_2441,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_2441) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22506,c_22506,c_22506,c_113])).

tff(c_25597,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22667,c_25595])).

tff(c_25600,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_25597])).

tff(c_22731,plain,(
    ! [C_2172,A_2173,B_2174] :
      ( v4_relat_1(C_2172,A_2173)
      | ~ m1_subset_1(C_2172,k1_zfmisc_1(k2_zfmisc_1(A_2173,B_2174))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22746,plain,(
    ! [A_2173] : v4_relat_1('#skF_4',A_2173) ),
    inference(resolution,[status(thm)],[c_22513,c_22731])).

tff(c_22863,plain,(
    ! [B_2195,A_2196] :
      ( k1_relat_1(B_2195) = A_2196
      | ~ v1_partfun1(B_2195,A_2196)
      | ~ v4_relat_1(B_2195,A_2196)
      | ~ v1_relat_1(B_2195) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_22866,plain,(
    ! [A_2173] :
      ( k1_relat_1('#skF_4') = A_2173
      | ~ v1_partfun1('#skF_4',A_2173)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22746,c_22863])).

tff(c_22869,plain,(
    ! [A_2173] :
      ( k1_relat_1('#skF_4') = A_2173
      | ~ v1_partfun1('#skF_4',A_2173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_22866])).

tff(c_25604,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25600,c_22869])).

tff(c_22888,plain,(
    ! [A_2206,B_2207,C_2208] :
      ( k1_relset_1(A_2206,B_2207,C_2208) = k1_relat_1(C_2208)
      | ~ m1_subset_1(C_2208,k1_zfmisc_1(k2_zfmisc_1(A_2206,B_2207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_22903,plain,(
    ! [A_2206,B_2207] : k1_relset_1(A_2206,B_2207,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22513,c_22888])).

tff(c_25605,plain,(
    ! [C_2443,A_2444,B_2445] :
      ( v1_funct_2(C_2443,A_2444,B_2445)
      | k1_relset_1(A_2444,B_2445,C_2443) != A_2444
      | ~ m1_subset_1(C_2443,k1_zfmisc_1(k2_zfmisc_1(A_2444,B_2445)))
      | ~ v1_funct_1(C_2443) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_25609,plain,(
    ! [A_2444,B_2445] :
      ( v1_funct_2('#skF_4',A_2444,B_2445)
      | k1_relset_1(A_2444,B_2445,'#skF_4') != A_2444
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22513,c_25605])).

tff(c_25622,plain,(
    ! [A_2444,B_2445] :
      ( v1_funct_2('#skF_4',A_2444,B_2445)
      | k1_relat_1('#skF_4') != A_2444 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22903,c_25609])).

tff(c_25672,plain,(
    ! [B_2445] : v1_funct_2('#skF_4','#skF_4',B_2445) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25604,c_25622])).

tff(c_26237,plain,(
    ! [D_2512,A_2513,B_2514] :
      ( v5_pre_topc(D_2512,A_2513,g1_pre_topc(u1_struct_0(B_2514),u1_pre_topc(B_2514)))
      | ~ v5_pre_topc(D_2512,A_2513,B_2514)
      | ~ m1_subset_1(D_2512,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2513),u1_struct_0(g1_pre_topc(u1_struct_0(B_2514),u1_pre_topc(B_2514))))))
      | ~ v1_funct_2(D_2512,u1_struct_0(A_2513),u1_struct_0(g1_pre_topc(u1_struct_0(B_2514),u1_pre_topc(B_2514))))
      | ~ m1_subset_1(D_2512,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2513),u1_struct_0(B_2514))))
      | ~ v1_funct_2(D_2512,u1_struct_0(A_2513),u1_struct_0(B_2514))
      | ~ v1_funct_1(D_2512)
      | ~ l1_pre_topc(B_2514)
      | ~ v2_pre_topc(B_2514)
      | ~ l1_pre_topc(A_2513)
      | ~ v2_pre_topc(A_2513) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_26262,plain,(
    ! [A_2513,B_2514] :
      ( v5_pre_topc('#skF_4',A_2513,g1_pre_topc(u1_struct_0(B_2514),u1_pre_topc(B_2514)))
      | ~ v5_pre_topc('#skF_4',A_2513,B_2514)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2513),u1_struct_0(g1_pre_topc(u1_struct_0(B_2514),u1_pre_topc(B_2514))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2513),u1_struct_0(B_2514))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2513),u1_struct_0(B_2514))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_2514)
      | ~ v2_pre_topc(B_2514)
      | ~ l1_pre_topc(A_2513)
      | ~ v2_pre_topc(A_2513) ) ),
    inference(resolution,[status(thm)],[c_22513,c_26237])).

tff(c_26469,plain,(
    ! [A_2519,B_2520] :
      ( v5_pre_topc('#skF_4',A_2519,g1_pre_topc(u1_struct_0(B_2520),u1_pre_topc(B_2520)))
      | ~ v5_pre_topc('#skF_4',A_2519,B_2520)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2519),u1_struct_0(g1_pre_topc(u1_struct_0(B_2520),u1_pre_topc(B_2520))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2519),u1_struct_0(B_2520))
      | ~ l1_pre_topc(B_2520)
      | ~ v2_pre_topc(B_2520)
      | ~ l1_pre_topc(A_2519)
      | ~ v2_pre_topc(A_2519) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_26262])).

tff(c_26493,plain,(
    ! [B_2520] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2520),u1_pre_topc(B_2520)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2520)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_2520),u1_pre_topc(B_2520))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2520))
      | ~ l1_pre_topc(B_2520)
      | ~ v2_pre_topc(B_2520)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22664,c_26469])).

tff(c_26511,plain,(
    ! [B_2520] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2520),u1_pre_topc(B_2520)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2520)
      | ~ l1_pre_topc(B_2520)
      | ~ v2_pre_topc(B_2520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_25672,c_22664,c_25672,c_26493])).

tff(c_26515,plain,(
    ! [B_2521] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2521),u1_pre_topc(B_2521)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2521)
      | ~ l1_pre_topc(B_2521)
      | ~ v2_pre_topc(B_2521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_25672,c_22664,c_25672,c_26493])).

tff(c_26524,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_25795,c_26515])).

tff(c_26536,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26467,c_25970,c_26524])).

tff(c_26543,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_26536])).

tff(c_26546,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26511,c_26543])).

tff(c_26550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_18959,c_26546])).

tff(c_26552,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_26536])).

tff(c_25651,plain,(
    ! [B_2449,C_2450,A_2451] :
      ( B_2449 = '#skF_4'
      | v1_partfun1(C_2450,A_2451)
      | ~ v1_funct_2(C_2450,A_2451,B_2449)
      | ~ m1_subset_1(C_2450,k1_zfmisc_1(k2_zfmisc_1(A_2451,B_2449)))
      | ~ v1_funct_1(C_2450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22506,c_58])).

tff(c_25655,plain,(
    ! [B_2449,A_2451] :
      ( B_2449 = '#skF_4'
      | v1_partfun1('#skF_4',A_2451)
      | ~ v1_funct_2('#skF_4',A_2451,B_2449)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22513,c_25651])).

tff(c_25681,plain,(
    ! [B_2454,A_2455] :
      ( B_2454 = '#skF_4'
      | v1_partfun1('#skF_4',A_2455)
      | ~ v1_funct_2('#skF_4',A_2455,B_2454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_25655])).

tff(c_25689,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_22668,c_25681])).

tff(c_25737,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_25689])).

tff(c_25625,plain,(
    ! [A_2173] :
      ( A_2173 = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_2173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25604,c_22869])).

tff(c_25742,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_25737,c_25625])).

tff(c_25910,plain,(
    ! [D_2477,A_2478,B_2479] :
      ( v5_pre_topc(D_2477,g1_pre_topc(u1_struct_0(A_2478),u1_pre_topc(A_2478)),B_2479)
      | ~ v5_pre_topc(D_2477,A_2478,B_2479)
      | ~ m1_subset_1(D_2477,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2478),u1_pre_topc(A_2478))),u1_struct_0(B_2479))))
      | ~ v1_funct_2(D_2477,u1_struct_0(g1_pre_topc(u1_struct_0(A_2478),u1_pre_topc(A_2478))),u1_struct_0(B_2479))
      | ~ m1_subset_1(D_2477,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2478),u1_struct_0(B_2479))))
      | ~ v1_funct_2(D_2477,u1_struct_0(A_2478),u1_struct_0(B_2479))
      | ~ v1_funct_1(D_2477)
      | ~ l1_pre_topc(B_2479)
      | ~ v2_pre_topc(B_2479)
      | ~ l1_pre_topc(A_2478)
      | ~ v2_pre_topc(A_2478) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_25935,plain,(
    ! [A_2478,B_2479] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2478),u1_pre_topc(A_2478)),B_2479)
      | ~ v5_pre_topc('#skF_4',A_2478,B_2479)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2478),u1_pre_topc(A_2478))),u1_struct_0(B_2479))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2478),u1_struct_0(B_2479))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2478),u1_struct_0(B_2479))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_2479)
      | ~ v2_pre_topc(B_2479)
      | ~ l1_pre_topc(A_2478)
      | ~ v2_pre_topc(A_2478) ) ),
    inference(resolution,[status(thm)],[c_22513,c_25910])).

tff(c_26691,plain,(
    ! [A_2533,B_2534] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2533),u1_pre_topc(A_2533)),B_2534)
      | ~ v5_pre_topc('#skF_4',A_2533,B_2534)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2533),u1_pre_topc(A_2533))),u1_struct_0(B_2534))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2533),u1_struct_0(B_2534))
      | ~ l1_pre_topc(B_2534)
      | ~ v2_pre_topc(B_2534)
      | ~ l1_pre_topc(A_2533)
      | ~ v2_pre_topc(A_2533) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_25935])).

tff(c_26715,plain,(
    ! [B_2534] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2534)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2534)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_2534))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2534))
      | ~ l1_pre_topc(B_2534)
      | ~ v2_pre_topc(B_2534)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22664,c_26691])).

tff(c_26736,plain,(
    ! [B_2535] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_2535)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2535)
      | ~ l1_pre_topc(B_2535)
      | ~ v2_pre_topc(B_2535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_25672,c_22664,c_25672,c_25742,c_22664,c_26715])).

tff(c_26742,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_26736,c_22830])).

tff(c_26747,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26467,c_25970,c_26552,c_26742])).

tff(c_26748,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_25689])).

tff(c_26768,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26748,c_22727])).

tff(c_26902,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_26768])).

tff(c_26910,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22727,c_26902])).

tff(c_26914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_26910])).

tff(c_26916,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_26768])).

tff(c_26762,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26748,c_66])).

tff(c_27218,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26916,c_26762])).

tff(c_27219,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_27218])).

tff(c_27222,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_27219])).

tff(c_27226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_27222])).

tff(c_27228,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_27218])).

tff(c_26750,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26748,c_22668])).

tff(c_26968,plain,(
    ! [D_2558,A_2559,B_2560] :
      ( v5_pre_topc(D_2558,A_2559,g1_pre_topc(u1_struct_0(B_2560),u1_pre_topc(B_2560)))
      | ~ v5_pre_topc(D_2558,A_2559,B_2560)
      | ~ m1_subset_1(D_2558,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2559),u1_struct_0(g1_pre_topc(u1_struct_0(B_2560),u1_pre_topc(B_2560))))))
      | ~ v1_funct_2(D_2558,u1_struct_0(A_2559),u1_struct_0(g1_pre_topc(u1_struct_0(B_2560),u1_pre_topc(B_2560))))
      | ~ m1_subset_1(D_2558,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2559),u1_struct_0(B_2560))))
      | ~ v1_funct_2(D_2558,u1_struct_0(A_2559),u1_struct_0(B_2560))
      | ~ v1_funct_1(D_2558)
      | ~ l1_pre_topc(B_2560)
      | ~ v2_pre_topc(B_2560)
      | ~ l1_pre_topc(A_2559)
      | ~ v2_pre_topc(A_2559) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_26987,plain,(
    ! [A_2559,B_2560] :
      ( v5_pre_topc('#skF_4',A_2559,g1_pre_topc(u1_struct_0(B_2560),u1_pre_topc(B_2560)))
      | ~ v5_pre_topc('#skF_4',A_2559,B_2560)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2559),u1_struct_0(g1_pre_topc(u1_struct_0(B_2560),u1_pre_topc(B_2560))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2559),u1_struct_0(B_2560))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2559),u1_struct_0(B_2560))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_2560)
      | ~ v2_pre_topc(B_2560)
      | ~ l1_pre_topc(A_2559)
      | ~ v2_pre_topc(A_2559) ) ),
    inference(resolution,[status(thm)],[c_22513,c_26968])).

tff(c_27387,plain,(
    ! [A_2597,B_2598] :
      ( v5_pre_topc('#skF_4',A_2597,g1_pre_topc(u1_struct_0(B_2598),u1_pre_topc(B_2598)))
      | ~ v5_pre_topc('#skF_4',A_2597,B_2598)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2597),u1_struct_0(g1_pre_topc(u1_struct_0(B_2598),u1_pre_topc(B_2598))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2597),u1_struct_0(B_2598))
      | ~ l1_pre_topc(B_2598)
      | ~ v2_pre_topc(B_2598)
      | ~ l1_pre_topc(A_2597)
      | ~ v2_pre_topc(A_2597) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_26987])).

tff(c_27405,plain,(
    ! [B_2598] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2598),u1_pre_topc(B_2598)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2598)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_2598),u1_pre_topc(B_2598))))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2598))
      | ~ l1_pre_topc(B_2598)
      | ~ v2_pre_topc(B_2598)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22664,c_27387])).

tff(c_27419,plain,(
    ! [B_2598] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2598),u1_pre_topc(B_2598)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2598)
      | ~ l1_pre_topc(B_2598)
      | ~ v2_pre_topc(B_2598) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_25672,c_22664,c_25672,c_27405])).

tff(c_22831,plain,(
    ! [A_2188,C_2189,B_2190] :
      ( m1_subset_1(A_2188,C_2189)
      | ~ m1_subset_1(B_2190,k1_zfmisc_1(C_2189))
      | ~ r2_hidden(A_2188,B_2190) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22842,plain,(
    ! [A_2188,A_45] :
      ( m1_subset_1(A_2188,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ r2_hidden(A_2188,u1_pre_topc(A_45))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_22831])).

tff(c_26756,plain,(
    ! [A_2188] :
      ( m1_subset_1(A_2188,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_2188,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26748,c_22842])).

tff(c_27122,plain,(
    ! [A_2573] :
      ( m1_subset_1(A_2573,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_2573,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26916,c_26756])).

tff(c_27127,plain,(
    ! [B_6] :
      ( m1_subset_1(B_6,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(B_6,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ) ),
    inference(resolution,[status(thm)],[c_14,c_27122])).

tff(c_27269,plain,(
    v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_27127])).

tff(c_27281,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_27269,c_22507])).

tff(c_27423,plain,(
    ! [B_2599] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_2599),u1_pre_topc(B_2599)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2599)
      | ~ l1_pre_topc(B_2599)
      | ~ v2_pre_topc(B_2599) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_25672,c_22664,c_25672,c_27405])).

tff(c_27429,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26748,c_27423])).

tff(c_27436,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27228,c_26916,c_27281,c_27429])).

tff(c_27439,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_27436])).

tff(c_27442,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_27419,c_27439])).

tff(c_27446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_18959,c_27442])).

tff(c_27448,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_27436])).

tff(c_27057,plain,(
    ! [D_2566,A_2567,B_2568] :
      ( v5_pre_topc(D_2566,g1_pre_topc(u1_struct_0(A_2567),u1_pre_topc(A_2567)),B_2568)
      | ~ v5_pre_topc(D_2566,A_2567,B_2568)
      | ~ m1_subset_1(D_2566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2567),u1_pre_topc(A_2567))),u1_struct_0(B_2568))))
      | ~ v1_funct_2(D_2566,u1_struct_0(g1_pre_topc(u1_struct_0(A_2567),u1_pre_topc(A_2567))),u1_struct_0(B_2568))
      | ~ m1_subset_1(D_2566,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2567),u1_struct_0(B_2568))))
      | ~ v1_funct_2(D_2566,u1_struct_0(A_2567),u1_struct_0(B_2568))
      | ~ v1_funct_1(D_2566)
      | ~ l1_pre_topc(B_2568)
      | ~ v2_pre_topc(B_2568)
      | ~ l1_pre_topc(A_2567)
      | ~ v2_pre_topc(A_2567) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_27076,plain,(
    ! [A_2567,B_2568] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2567),u1_pre_topc(A_2567)),B_2568)
      | ~ v5_pre_topc('#skF_4',A_2567,B_2568)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2567),u1_pre_topc(A_2567))),u1_struct_0(B_2568))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2567),u1_struct_0(B_2568))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2567),u1_struct_0(B_2568))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_2568)
      | ~ v2_pre_topc(B_2568)
      | ~ l1_pre_topc(A_2567)
      | ~ v2_pre_topc(A_2567) ) ),
    inference(resolution,[status(thm)],[c_22513,c_27057])).

tff(c_27239,plain,(
    ! [A_2593,B_2594] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_2593),u1_pre_topc(A_2593)),B_2594)
      | ~ v5_pre_topc('#skF_4',A_2593,B_2594)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_2593),u1_pre_topc(A_2593))),u1_struct_0(B_2594))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_2593),u1_struct_0(B_2594))
      | ~ l1_pre_topc(B_2594)
      | ~ v2_pre_topc(B_2594)
      | ~ l1_pre_topc(A_2593)
      | ~ v2_pre_topc(A_2593) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_27076])).

tff(c_27254,plain,(
    ! [B_2594] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_2594)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2594)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_2594))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_2594))
      | ~ l1_pre_topc(B_2594)
      | ~ v2_pre_topc(B_2594)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22664,c_27239])).

tff(c_27896,plain,(
    ! [B_2621] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),B_2621)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_2621)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_2621))
      | ~ l1_pre_topc(B_2621)
      | ~ v2_pre_topc(B_2621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_25672,c_22664,c_22664,c_27254])).

tff(c_27899,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26748,c_27896])).

tff(c_27907,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27228,c_26916,c_26750,c_27448,c_27899])).

tff(c_27909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22830,c_27907])).

tff(c_27910,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_22659])).

tff(c_27914,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27910,c_107])).

tff(c_37502,plain,(
    ! [A_3505,B_3506,C_3507] :
      ( k1_relset_1(A_3505,B_3506,C_3507) = k1_relat_1(C_3507)
      | ~ m1_subset_1(C_3507,k1_zfmisc_1(k2_zfmisc_1(A_3505,B_3506))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_37517,plain,(
    ! [A_3505,B_3506] : k1_relset_1(A_3505,B_3506,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22513,c_37502])).

tff(c_39008,plain,(
    ! [C_3689,A_3690,B_3691] :
      ( v1_funct_2(C_3689,A_3690,B_3691)
      | k1_relset_1(A_3690,B_3691,C_3689) != A_3690
      | ~ m1_subset_1(C_3689,k1_zfmisc_1(k2_zfmisc_1(A_3690,B_3691)))
      | ~ v1_funct_1(C_3689) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_39012,plain,(
    ! [A_3690,B_3691] :
      ( v1_funct_2('#skF_4',A_3690,B_3691)
      | k1_relset_1(A_3690,B_3691,'#skF_4') != A_3690
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22513,c_39008])).

tff(c_39025,plain,(
    ! [A_3690,B_3691] :
      ( v1_funct_2('#skF_4',A_3690,B_3691)
      | k1_relat_1('#skF_4') != A_3690 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_37517,c_39012])).

tff(c_39077,plain,(
    ! [C_3699,A_3700,B_3701] :
      ( ~ v1_xboole_0(C_3699)
      | ~ v1_funct_2(C_3699,A_3700,B_3701)
      | ~ v1_funct_1(C_3699)
      | ~ m1_subset_1(C_3699,k1_zfmisc_1(k2_zfmisc_1(A_3700,B_3701)))
      | v1_xboole_0(B_3701)
      | v1_xboole_0(A_3700) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_39081,plain,(
    ! [A_3700,B_3701] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_3700,B_3701)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_3701)
      | v1_xboole_0(A_3700) ) ),
    inference(resolution,[status(thm)],[c_22513,c_39077])).

tff(c_39098,plain,(
    ! [A_3702,B_3703] :
      ( ~ v1_funct_2('#skF_4',A_3702,B_3703)
      | v1_xboole_0(B_3703)
      | v1_xboole_0(A_3702) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22499,c_39081])).

tff(c_39105,plain,(
    ! [B_3691,A_3690] :
      ( v1_xboole_0(B_3691)
      | v1_xboole_0(A_3690)
      | k1_relat_1('#skF_4') != A_3690 ) ),
    inference(resolution,[status(thm)],[c_39025,c_39098])).

tff(c_39110,plain,(
    ! [A_3704] :
      ( v1_xboole_0(A_3704)
      | k1_relat_1('#skF_4') != A_3704 ) ),
    inference(splitLeft,[status(thm)],[c_39105])).

tff(c_39169,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_39110,c_22507])).

tff(c_39029,plain,(
    ! [A_3692,B_3693] :
      ( v1_funct_2('#skF_4',A_3692,B_3693)
      | k1_relat_1('#skF_4') != A_3692 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_37517,c_39012])).

tff(c_37610,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22506,c_22506,c_22506,c_113])).

tff(c_39035,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_39029,c_37610])).

tff(c_39042,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_39035])).

tff(c_39044,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_39042])).

tff(c_39183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39169,c_39044])).

tff(c_39184,plain,(
    ! [B_3691] : v1_xboole_0(B_3691) ),
    inference(splitRight,[status(thm)],[c_39105])).

tff(c_22515,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22506,c_22506,c_8])).

tff(c_27915,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27910,c_82])).

tff(c_37542,plain,(
    ! [C_3513,A_3514,B_3515] :
      ( v1_partfun1(C_3513,A_3514)
      | ~ v1_funct_2(C_3513,A_3514,B_3515)
      | ~ v1_funct_1(C_3513)
      | ~ m1_subset_1(C_3513,k1_zfmisc_1(k2_zfmisc_1(A_3514,B_3515)))
      | v1_xboole_0(B_3515) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_37546,plain,(
    ! [A_3514,B_3515] :
      ( v1_partfun1('#skF_4',A_3514)
      | ~ v1_funct_2('#skF_4',A_3514,B_3515)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_3515) ) ),
    inference(resolution,[status(thm)],[c_22513,c_37542])).

tff(c_37562,plain,(
    ! [A_3516,B_3517] :
      ( v1_partfun1('#skF_4',A_3516)
      | ~ v1_funct_2('#skF_4',A_3516,B_3517)
      | v1_xboole_0(B_3517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_37546])).

tff(c_37569,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_27915,c_37562])).

tff(c_37627,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_37569])).

tff(c_37640,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_37627,c_22507])).

tff(c_38136,plain,(
    ! [D_3573,A_3574,B_3575] :
      ( v5_pre_topc(D_3573,A_3574,g1_pre_topc(u1_struct_0(B_3575),u1_pre_topc(B_3575)))
      | ~ v5_pre_topc(D_3573,A_3574,B_3575)
      | ~ m1_subset_1(D_3573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574),u1_struct_0(g1_pre_topc(u1_struct_0(B_3575),u1_pre_topc(B_3575))))))
      | ~ v1_funct_2(D_3573,u1_struct_0(A_3574),u1_struct_0(g1_pre_topc(u1_struct_0(B_3575),u1_pre_topc(B_3575))))
      | ~ m1_subset_1(D_3573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574),u1_struct_0(B_3575))))
      | ~ v1_funct_2(D_3573,u1_struct_0(A_3574),u1_struct_0(B_3575))
      | ~ v1_funct_1(D_3573)
      | ~ l1_pre_topc(B_3575)
      | ~ v2_pre_topc(B_3575)
      | ~ l1_pre_topc(A_3574)
      | ~ v2_pre_topc(A_3574) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_38148,plain,(
    ! [D_3573,A_3574] :
      ( v5_pre_topc(D_3573,A_3574,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_3573,A_3574,'#skF_2')
      | ~ m1_subset_1(D_3573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_3573,u1_struct_0(A_3574),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_3573,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_3573,u1_struct_0(A_3574),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_3573)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_3574)
      | ~ v2_pre_topc(A_3574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27910,c_38136])).

tff(c_38878,plain,(
    ! [D_3679,A_3680] :
      ( v5_pre_topc(D_3679,A_3680,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_3679,A_3680,'#skF_2')
      | ~ m1_subset_1(D_3679,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_3679,u1_struct_0(A_3680),'#skF_4')
      | ~ v1_funct_1(D_3679)
      | ~ l1_pre_topc(A_3680)
      | ~ v2_pre_topc(A_3680) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_27910,c_22515,c_27910,c_37640,c_27910,c_22515,c_37640,c_27910,c_38148])).

tff(c_37644,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37640,c_27915])).

tff(c_33834,plain,(
    ! [A_3158] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_3158),u1_pre_topc(A_3158)))
      | ~ l1_pre_topc(A_3158)
      | ~ v2_pre_topc(A_3158) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_33837,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27910,c_33834])).

tff(c_33839,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_33837])).

tff(c_27921,plain,(
    ! [A_2622] :
      ( m1_subset_1(u1_pre_topc(A_2622),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2622))))
      | ~ l1_pre_topc(A_2622) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_27933,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27910,c_27921])).

tff(c_27938,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_27933])).

tff(c_27976,plain,(
    ! [A_2627,B_2628] :
      ( l1_pre_topc(g1_pre_topc(A_2627,B_2628))
      | ~ m1_subset_1(B_2628,k1_zfmisc_1(k1_zfmisc_1(A_2627))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_27991,plain,(
    l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_27938,c_27976])).

tff(c_38195,plain,(
    ! [D_3583,A_3584,B_3585] :
      ( v5_pre_topc(D_3583,g1_pre_topc(u1_struct_0(A_3584),u1_pre_topc(A_3584)),B_3585)
      | ~ v5_pre_topc(D_3583,A_3584,B_3585)
      | ~ m1_subset_1(D_3583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3584),u1_pre_topc(A_3584))),u1_struct_0(B_3585))))
      | ~ v1_funct_2(D_3583,u1_struct_0(g1_pre_topc(u1_struct_0(A_3584),u1_pre_topc(A_3584))),u1_struct_0(B_3585))
      | ~ m1_subset_1(D_3583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3584),u1_struct_0(B_3585))))
      | ~ v1_funct_2(D_3583,u1_struct_0(A_3584),u1_struct_0(B_3585))
      | ~ v1_funct_1(D_3583)
      | ~ l1_pre_topc(B_3585)
      | ~ v2_pre_topc(B_3585)
      | ~ l1_pre_topc(A_3584)
      | ~ v2_pre_topc(A_3584) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_38201,plain,(
    ! [D_3583,A_3584] :
      ( v5_pre_topc(D_3583,g1_pre_topc(u1_struct_0(A_3584),u1_pre_topc(A_3584)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_3583,A_3584,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_3583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3584),u1_pre_topc(A_3584))),'#skF_4')))
      | ~ v1_funct_2(D_3583,u1_struct_0(g1_pre_topc(u1_struct_0(A_3584),u1_pre_topc(A_3584))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_3583,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3584),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_3583,u1_struct_0(A_3584),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1(D_3583)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_3584)
      | ~ v2_pre_topc(A_3584) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37640,c_38195])).

tff(c_38265,plain,(
    ! [D_3589,A_3590] :
      ( v5_pre_topc(D_3589,g1_pre_topc(u1_struct_0(A_3590),u1_pre_topc(A_3590)),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_3589,A_3590,g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(D_3589,u1_struct_0(g1_pre_topc(u1_struct_0(A_3590),u1_pre_topc(A_3590))),'#skF_4')
      | ~ m1_subset_1(D_3589,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_3589,u1_struct_0(A_3590),'#skF_4')
      | ~ v1_funct_1(D_3589)
      | ~ l1_pre_topc(A_3590)
      | ~ v2_pre_topc(A_3590) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33839,c_27991,c_37640,c_22515,c_37640,c_37640,c_22515,c_38201])).

tff(c_33767,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27910,c_18960])).

tff(c_38268,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38265,c_33767])).

tff(c_38277,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_27914,c_22513,c_37644,c_38268])).

tff(c_38900,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38878,c_38277])).

tff(c_38918,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_27914,c_22513,c_18959,c_38900])).

tff(c_38920,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_37569])).

tff(c_39239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39184,c_38920])).

tff(c_39241,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_39042])).

tff(c_39340,plain,(
    ! [B_3691] : v1_funct_2('#skF_4','#skF_4',B_3691) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39241,c_39025])).

tff(c_38919,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_37569])).

tff(c_27959,plain,(
    ! [C_2624,A_2625,B_2626] :
      ( v4_relat_1(C_2624,A_2625)
      | ~ m1_subset_1(C_2624,k1_zfmisc_1(k2_zfmisc_1(A_2625,B_2626))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_27974,plain,(
    ! [A_2625] : v4_relat_1('#skF_4',A_2625) ),
    inference(resolution,[status(thm)],[c_22513,c_27959])).

tff(c_33857,plain,(
    ! [B_3168,A_3169] :
      ( k1_relat_1(B_3168) = A_3169
      | ~ v1_partfun1(B_3168,A_3169)
      | ~ v4_relat_1(B_3168,A_3169)
      | ~ v1_relat_1(B_3168) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_33860,plain,(
    ! [A_2625] :
      ( k1_relat_1('#skF_4') = A_2625
      | ~ v1_partfun1('#skF_4',A_2625)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_27974,c_33857])).

tff(c_33863,plain,(
    ! [A_2625] :
      ( k1_relat_1('#skF_4') = A_2625
      | ~ v1_partfun1('#skF_4',A_2625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_33860])).

tff(c_38924,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_38919,c_33863])).

tff(c_39269,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39241,c_38924])).

tff(c_39556,plain,(
    ! [D_3730,A_3731,B_3732] :
      ( v5_pre_topc(D_3730,g1_pre_topc(u1_struct_0(A_3731),u1_pre_topc(A_3731)),B_3732)
      | ~ v5_pre_topc(D_3730,A_3731,B_3732)
      | ~ m1_subset_1(D_3730,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3731),u1_pre_topc(A_3731))),u1_struct_0(B_3732))))
      | ~ v1_funct_2(D_3730,u1_struct_0(g1_pre_topc(u1_struct_0(A_3731),u1_pre_topc(A_3731))),u1_struct_0(B_3732))
      | ~ m1_subset_1(D_3730,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3731),u1_struct_0(B_3732))))
      | ~ v1_funct_2(D_3730,u1_struct_0(A_3731),u1_struct_0(B_3732))
      | ~ v1_funct_1(D_3730)
      | ~ l1_pre_topc(B_3732)
      | ~ v2_pre_topc(B_3732)
      | ~ l1_pre_topc(A_3731)
      | ~ v2_pre_topc(A_3731) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_39575,plain,(
    ! [A_3731,B_3732] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_3731),u1_pre_topc(A_3731)),B_3732)
      | ~ v5_pre_topc('#skF_4',A_3731,B_3732)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_3731),u1_pre_topc(A_3731))),u1_struct_0(B_3732))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3731),u1_struct_0(B_3732))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3731),u1_struct_0(B_3732))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_3732)
      | ~ v2_pre_topc(B_3732)
      | ~ l1_pre_topc(A_3731)
      | ~ v2_pre_topc(A_3731) ) ),
    inference(resolution,[status(thm)],[c_22513,c_39556])).

tff(c_40167,plain,(
    ! [A_3812,B_3813] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_3812),u1_pre_topc(A_3812)),B_3813)
      | ~ v5_pre_topc('#skF_4',A_3812,B_3813)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_3812),u1_pre_topc(A_3812))),u1_struct_0(B_3813))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3812),u1_struct_0(B_3813))
      | ~ l1_pre_topc(B_3813)
      | ~ v2_pre_topc(B_3813)
      | ~ l1_pre_topc(A_3812)
      | ~ v2_pre_topc(A_3812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_39575])).

tff(c_40179,plain,(
    ! [B_3813] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3813)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3813)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_3813))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_3813))
      | ~ l1_pre_topc(B_3813)
      | ~ v2_pre_topc(B_3813)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39269,c_40167])).

tff(c_40195,plain,(
    ! [B_3813] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3813)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_3813)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_3813))
      | ~ l1_pre_topc(B_3813)
      | ~ v2_pre_topc(B_3813) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_39340,c_40179])).

tff(c_27992,plain,(
    ! [A_45] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_27976])).

tff(c_38966,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_38924,c_27992])).

tff(c_38993,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_38966])).

tff(c_38996,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_27992,c_38993])).

tff(c_39000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_38996])).

tff(c_39002,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_38966])).

tff(c_39302,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_39269,c_66])).

tff(c_39324,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39002,c_39302])).

tff(c_39766,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_39324])).

tff(c_39769,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_39766])).

tff(c_39773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_39769])).

tff(c_39775,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_39324])).

tff(c_39482,plain,(
    ! [D_3723,A_3724,B_3725] :
      ( v5_pre_topc(D_3723,A_3724,g1_pre_topc(u1_struct_0(B_3725),u1_pre_topc(B_3725)))
      | ~ v5_pre_topc(D_3723,A_3724,B_3725)
      | ~ m1_subset_1(D_3723,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3724),u1_struct_0(g1_pre_topc(u1_struct_0(B_3725),u1_pre_topc(B_3725))))))
      | ~ v1_funct_2(D_3723,u1_struct_0(A_3724),u1_struct_0(g1_pre_topc(u1_struct_0(B_3725),u1_pre_topc(B_3725))))
      | ~ m1_subset_1(D_3723,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3724),u1_struct_0(B_3725))))
      | ~ v1_funct_2(D_3723,u1_struct_0(A_3724),u1_struct_0(B_3725))
      | ~ v1_funct_1(D_3723)
      | ~ l1_pre_topc(B_3725)
      | ~ v2_pre_topc(B_3725)
      | ~ l1_pre_topc(A_3724)
      | ~ v2_pre_topc(A_3724) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_39501,plain,(
    ! [A_3724,B_3725] :
      ( v5_pre_topc('#skF_4',A_3724,g1_pre_topc(u1_struct_0(B_3725),u1_pre_topc(B_3725)))
      | ~ v5_pre_topc('#skF_4',A_3724,B_3725)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3724),u1_struct_0(g1_pre_topc(u1_struct_0(B_3725),u1_pre_topc(B_3725))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3724),u1_struct_0(B_3725))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3724),u1_struct_0(B_3725))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_3725)
      | ~ v2_pre_topc(B_3725)
      | ~ l1_pre_topc(A_3724)
      | ~ v2_pre_topc(A_3724) ) ),
    inference(resolution,[status(thm)],[c_22513,c_39482])).

tff(c_40270,plain,(
    ! [A_3820,B_3821] :
      ( v5_pre_topc('#skF_4',A_3820,g1_pre_topc(u1_struct_0(B_3821),u1_pre_topc(B_3821)))
      | ~ v5_pre_topc('#skF_4',A_3820,B_3821)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3820),u1_struct_0(g1_pre_topc(u1_struct_0(B_3821),u1_pre_topc(B_3821))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_3820),u1_struct_0(B_3821))
      | ~ l1_pre_topc(B_3821)
      | ~ v2_pre_topc(B_3821)
      | ~ l1_pre_topc(A_3820)
      | ~ v2_pre_topc(A_3820) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22513,c_39501])).

tff(c_40279,plain,(
    ! [B_3821] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_3821),u1_pre_topc(B_3821)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3821)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_3821),u1_pre_topc(B_3821))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_3821))
      | ~ l1_pre_topc(B_3821)
      | ~ v2_pre_topc(B_3821)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39269,c_40270])).

tff(c_40329,plain,(
    ! [B_3823] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_3823),u1_pre_topc(B_3823)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_3823)
      | ~ l1_pre_topc(B_3823)
      | ~ v2_pre_topc(B_3823) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39775,c_39002,c_39340,c_39269,c_39340,c_40279])).

tff(c_40341,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27910,c_40329])).

tff(c_40348,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_40341])).

tff(c_40349,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_33767,c_40348])).

tff(c_40352,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40195,c_40349])).

tff(c_40356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_27914,c_27910,c_18959,c_40352])).

tff(c_40358,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_40375,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40358,c_144])).

tff(c_44107,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44094,c_44094,c_40375])).

tff(c_44112,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44094,c_44094,c_10])).

tff(c_44111,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44094,c_20])).

tff(c_44469,plain,(
    ! [A_4255,B_4256,C_4257] :
      ( k1_relset_1(A_4255,B_4256,C_4257) = k1_relat_1(C_4257)
      | ~ m1_subset_1(C_4257,k1_zfmisc_1(k2_zfmisc_1(A_4255,B_4256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44484,plain,(
    ! [A_4255,B_4256] : k1_relset_1(A_4255,B_4256,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44111,c_44469])).

tff(c_44594,plain,(
    ! [C_4284,A_4285,B_4286] :
      ( v1_funct_2(C_4284,A_4285,B_4286)
      | k1_relset_1(A_4285,B_4286,C_4284) != A_4285
      | ~ m1_subset_1(C_4284,k1_zfmisc_1(k2_zfmisc_1(A_4285,B_4286)))
      | ~ v1_funct_1(C_4284) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_44598,plain,(
    ! [A_4285,B_4286] :
      ( v1_funct_2('#skF_4',A_4285,B_4286)
      | k1_relset_1(A_4285,B_4286,'#skF_4') != A_4285
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44111,c_44594])).

tff(c_44611,plain,(
    ! [A_4285,B_4286] :
      ( v1_funct_2('#skF_4',A_4285,B_4286)
      | k1_relat_1('#skF_4') != A_4285 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_44484,c_44598])).

tff(c_45465,plain,(
    ! [C_4326,A_4327,B_4328] :
      ( ~ v1_xboole_0(C_4326)
      | ~ v1_funct_2(C_4326,A_4327,B_4328)
      | ~ v1_funct_1(C_4326)
      | ~ m1_subset_1(C_4326,k1_zfmisc_1(k2_zfmisc_1(A_4327,B_4328)))
      | v1_xboole_0(B_4328)
      | v1_xboole_0(A_4327) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_45469,plain,(
    ! [A_4327,B_4328] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_4327,B_4328)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_4328)
      | v1_xboole_0(A_4327) ) ),
    inference(resolution,[status(thm)],[c_44111,c_45465])).

tff(c_45572,plain,(
    ! [A_4334,B_4335] :
      ( ~ v1_funct_2('#skF_4',A_4334,B_4335)
      | v1_xboole_0(B_4335)
      | v1_xboole_0(A_4334) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_44082,c_45469])).

tff(c_45581,plain,(
    ! [B_4286,A_4285] :
      ( v1_xboole_0(B_4286)
      | v1_xboole_0(A_4285)
      | k1_relat_1('#skF_4') != A_4285 ) ),
    inference(resolution,[status(thm)],[c_44611,c_45572])).

tff(c_45585,plain,(
    ! [A_4336] :
      ( v1_xboole_0(A_4336)
      | k1_relat_1('#skF_4') != A_4336 ) ),
    inference(splitLeft,[status(thm)],[c_45581])).

tff(c_44095,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_44082,c_4])).

tff(c_45633,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_45585,c_44095])).

tff(c_44647,plain,(
    ! [C_4294,A_4295,B_4296] :
      ( v1_partfun1(C_4294,A_4295)
      | ~ v1_funct_2(C_4294,A_4295,B_4296)
      | ~ v1_funct_1(C_4294)
      | ~ m1_subset_1(C_4294,k1_zfmisc_1(k2_zfmisc_1(A_4295,B_4296)))
      | v1_xboole_0(B_4296) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_44651,plain,(
    ! [A_4295,B_4296] :
      ( v1_partfun1('#skF_4',A_4295)
      | ~ v1_funct_2('#skF_4',A_4295,B_4296)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_4296) ) ),
    inference(resolution,[status(thm)],[c_44111,c_44647])).

tff(c_44668,plain,(
    ! [A_4297,B_4298] :
      ( v1_partfun1('#skF_4',A_4297)
      | ~ v1_funct_2('#skF_4',A_4297,B_4298)
      | v1_xboole_0(B_4298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_44651])).

tff(c_44677,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_44668])).

tff(c_44683,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40561,c_44677])).

tff(c_44113,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44094,c_44094,c_8])).

tff(c_44436,plain,(
    ! [B_4247,A_4248,B_4249] :
      ( v4_relat_1(B_4247,A_4248)
      | ~ v1_xboole_0(B_4247)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(A_4248,B_4249))) ) ),
    inference(resolution,[status(thm)],[c_16,c_40504])).

tff(c_44438,plain,(
    ! [B_4247,A_3] :
      ( v4_relat_1(B_4247,A_3)
      | ~ v1_xboole_0(B_4247)
      | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44113,c_44436])).

tff(c_44445,plain,(
    ! [B_4250,A_4251] :
      ( v4_relat_1(B_4250,A_4251)
      | ~ v1_xboole_0(B_4250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44082,c_44107,c_44438])).

tff(c_48,plain,(
    ! [B_36,A_35] :
      ( k1_relat_1(B_36) = A_35
      | ~ v1_partfun1(B_36,A_35)
      | ~ v4_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44453,plain,(
    ! [B_4250,A_4251] :
      ( k1_relat_1(B_4250) = A_4251
      | ~ v1_partfun1(B_4250,A_4251)
      | ~ v1_relat_1(B_4250)
      | ~ v1_xboole_0(B_4250) ) ),
    inference(resolution,[status(thm)],[c_44445,c_48])).

tff(c_44686,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_44683,c_44453])).

tff(c_44692,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44082,c_220,c_44686])).

tff(c_18,plain,(
    ! [B_6,A_5] :
      ( v1_xboole_0(B_6)
      | ~ m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_180,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_111,c_18])).

tff(c_40564,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_44696,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44692,c_40564])).

tff(c_45643,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45633,c_44696])).

tff(c_45655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44082,c_44107,c_44112,c_45643])).

tff(c_45656,plain,(
    ! [B_4286] : v1_xboole_0(B_4286) ),
    inference(splitRight,[status(thm)],[c_45581])).

tff(c_45719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45656,c_44696])).

tff(c_45720,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_45732,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_45720,c_144])).

tff(c_45750,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45732,c_45732,c_10])).

tff(c_45749,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45732,c_20])).

tff(c_46057,plain,(
    ! [A_4371,B_4372,C_4373] :
      ( k1_relset_1(A_4371,B_4372,C_4373) = k1_relat_1(C_4373)
      | ~ m1_subset_1(C_4373,k1_zfmisc_1(k2_zfmisc_1(A_4371,B_4372))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46075,plain,(
    ! [A_4371,B_4372] : k1_relset_1(A_4371,B_4372,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45749,c_46057])).

tff(c_46292,plain,(
    ! [C_4409,A_4410,B_4411] :
      ( v1_funct_2(C_4409,A_4410,B_4411)
      | k1_relset_1(A_4410,B_4411,C_4409) != A_4410
      | ~ m1_subset_1(C_4409,k1_zfmisc_1(k2_zfmisc_1(A_4410,B_4411)))
      | ~ v1_funct_1(C_4409) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46296,plain,(
    ! [A_4410,B_4411] :
      ( v1_funct_2('#skF_4',A_4410,B_4411)
      | k1_relset_1(A_4410,B_4411,'#skF_4') != A_4410
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_45749,c_46292])).

tff(c_46309,plain,(
    ! [A_4410,B_4411] :
      ( v1_funct_2('#skF_4',A_4410,B_4411)
      | k1_relat_1('#skF_4') != A_4410 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46075,c_46296])).

tff(c_47160,plain,(
    ! [C_4445,A_4446,B_4447] :
      ( ~ v1_xboole_0(C_4445)
      | ~ v1_funct_2(C_4445,A_4446,B_4447)
      | ~ v1_funct_1(C_4445)
      | ~ m1_subset_1(C_4445,k1_zfmisc_1(k2_zfmisc_1(A_4446,B_4447)))
      | v1_xboole_0(B_4447)
      | v1_xboole_0(A_4446) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_47167,plain,(
    ! [A_4446,B_4447] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_4446,B_4447)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_4447)
      | v1_xboole_0(A_4446) ) ),
    inference(resolution,[status(thm)],[c_45749,c_47160])).

tff(c_47192,plain,(
    ! [A_4449,B_4450] :
      ( ~ v1_funct_2('#skF_4',A_4449,B_4450)
      | v1_xboole_0(B_4450)
      | v1_xboole_0(A_4449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_45720,c_47167])).

tff(c_47196,plain,(
    ! [B_4411,A_4410] :
      ( v1_xboole_0(B_4411)
      | v1_xboole_0(A_4410)
      | k1_relat_1('#skF_4') != A_4410 ) ),
    inference(resolution,[status(thm)],[c_46309,c_47192])).

tff(c_47209,plain,(
    ! [A_4451] :
      ( v1_xboole_0(A_4451)
      | k1_relat_1('#skF_4') != A_4451 ) ),
    inference(splitLeft,[status(thm)],[c_47196])).

tff(c_45733,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_45720,c_4])).

tff(c_47245,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47209,c_45733])).

tff(c_40388,plain,(
    m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40375,c_20])).

tff(c_45744,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45732,c_45732,c_40388])).

tff(c_46315,plain,(
    ! [A_4412,B_4413] :
      ( v1_funct_2('#skF_4',A_4412,B_4413)
      | k1_relat_1('#skF_4') != A_4412 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46075,c_46296])).

tff(c_45745,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45732,c_45732,c_40375])).

tff(c_46164,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,'#skF_4')
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45745,c_45732,c_45732,c_45732,c_113])).

tff(c_46322,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_46315,c_46164])).

tff(c_46326,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_45744,c_46322])).

tff(c_46327,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46326])).

tff(c_47264,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47245,c_46327])).

tff(c_47265,plain,(
    ! [B_4411] : v1_xboole_0(B_4411) ),
    inference(splitRight,[status(thm)],[c_47196])).

tff(c_46204,plain,(
    ! [C_4404,A_4405,B_4406] :
      ( v1_partfun1(C_4404,A_4405)
      | ~ v1_funct_2(C_4404,A_4405,B_4406)
      | ~ v1_funct_1(C_4404)
      | ~ m1_subset_1(C_4404,k1_zfmisc_1(k2_zfmisc_1(A_4405,B_4406)))
      | v1_xboole_0(B_4406) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_46211,plain,(
    ! [A_4405,B_4406] :
      ( v1_partfun1('#skF_4',A_4405)
      | ~ v1_funct_2('#skF_4',A_4405,B_4406)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_4406) ) ),
    inference(resolution,[status(thm)],[c_45749,c_46204])).

tff(c_46229,plain,(
    ! [A_4407,B_4408] :
      ( v1_partfun1('#skF_4',A_4407)
      | ~ v1_funct_2('#skF_4',A_4407,B_4408)
      | v1_xboole_0(B_4408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_46211])).

tff(c_46232,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_46229])).

tff(c_46238,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40561,c_46232])).

tff(c_40528,plain,(
    ! [A_3845] : v4_relat_1(k1_xboole_0,A_3845) ),
    inference(resolution,[status(thm)],[c_20,c_40504])).

tff(c_45735,plain,(
    ! [A_3845] : v4_relat_1('#skF_4',A_3845) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45732,c_40528])).

tff(c_46012,plain,(
    ! [B_4361,A_4362] :
      ( k1_relat_1(B_4361) = A_4362
      | ~ v1_partfun1(B_4361,A_4362)
      | ~ v4_relat_1(B_4361,A_4362)
      | ~ v1_relat_1(B_4361) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_46018,plain,(
    ! [A_3845] :
      ( k1_relat_1('#skF_4') = A_3845
      | ~ v1_partfun1('#skF_4',A_3845)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_45735,c_46012])).

tff(c_46022,plain,(
    ! [A_3845] :
      ( k1_relat_1('#skF_4') = A_3845
      | ~ v1_partfun1('#skF_4',A_3845) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_46018])).

tff(c_46243,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46238,c_46022])).

tff(c_40450,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_46248,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46243,c_40450])).

tff(c_47311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47265,c_46248])).

tff(c_47313,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46326])).

tff(c_47345,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47313,c_46248])).

tff(c_47353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_45720,c_45750,c_47345])).

tff(c_47354,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_40554])).

tff(c_47366,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47354,c_144])).

tff(c_47384,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47366,c_47366,c_8])).

tff(c_47355,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_40554])).

tff(c_47438,plain,(
    ! [A_4460] :
      ( A_4460 = '#skF_4'
      | ~ v1_xboole_0(A_4460) ) ),
    inference(resolution,[status(thm)],[c_47354,c_4])).

tff(c_47445,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47355,c_47438])).

tff(c_47450,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47445,c_40450])).

tff(c_47663,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_47354,c_47384,c_47450])).

tff(c_47664,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_47676,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47664,c_144])).

tff(c_47682,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_47676,c_40388])).

tff(c_47665,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_47677,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_47664,c_4])).

tff(c_47855,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47665,c_47677])).

tff(c_47925,plain,(
    ! [B_4499,A_4500] :
      ( B_4499 = '#skF_4'
      | A_4500 = '#skF_4'
      | k2_zfmisc_1(A_4500,B_4499) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_47676,c_47676,c_6])).

tff(c_47935,plain,
    ( u1_struct_0('#skF_2') = '#skF_4'
    | u1_struct_0('#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_47855,c_47925])).

tff(c_47940,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_47935])).

tff(c_47943,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47940,c_107])).

tff(c_47683,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_47676,c_40375])).

tff(c_48193,plain,(
    ! [C_4535,B_4536] :
      ( v1_partfun1(C_4535,'#skF_4')
      | ~ v1_funct_2(C_4535,'#skF_4',B_4536)
      | ~ m1_subset_1(C_4535,'#skF_4')
      | ~ v1_funct_1(C_4535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47683,c_47676,c_47676,c_47676,c_113])).

tff(c_48196,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47943,c_48193])).

tff(c_48199,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47682,c_48196])).

tff(c_47687,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_20])).

tff(c_47858,plain,(
    ! [C_4482,A_4483,B_4484] :
      ( v4_relat_1(C_4482,A_4483)
      | ~ m1_subset_1(C_4482,k1_zfmisc_1(k2_zfmisc_1(A_4483,B_4484))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_47873,plain,(
    ! [A_4483] : v4_relat_1('#skF_4',A_4483) ),
    inference(resolution,[status(thm)],[c_47687,c_47858])).

tff(c_48096,plain,(
    ! [B_4517,A_4518] :
      ( k1_relat_1(B_4517) = A_4518
      | ~ v1_partfun1(B_4517,A_4518)
      | ~ v4_relat_1(B_4517,A_4518)
      | ~ v1_relat_1(B_4517) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48102,plain,(
    ! [A_4483] :
      ( k1_relat_1('#skF_4') = A_4483
      | ~ v1_partfun1('#skF_4',A_4483)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47873,c_48096])).

tff(c_48106,plain,(
    ! [A_4483] :
      ( k1_relat_1('#skF_4') = A_4483
      | ~ v1_partfun1('#skF_4',A_4483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_48102])).

tff(c_48203,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48199,c_48106])).

tff(c_48131,plain,(
    ! [A_4524,B_4525,C_4526] :
      ( k1_relset_1(A_4524,B_4525,C_4526) = k1_relat_1(C_4526)
      | ~ m1_subset_1(C_4526,k1_zfmisc_1(k2_zfmisc_1(A_4524,B_4525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48146,plain,(
    ! [A_4524,B_4525] : k1_relset_1(A_4524,B_4525,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47687,c_48131])).

tff(c_48204,plain,(
    ! [A_4524,B_4525] : k1_relset_1(A_4524,B_4525,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48203,c_48146])).

tff(c_49578,plain,(
    ! [C_4681,A_4682,B_4683] :
      ( v1_funct_2(C_4681,A_4682,B_4683)
      | k1_relset_1(A_4682,B_4683,C_4681) != A_4682
      | ~ m1_subset_1(C_4681,k1_zfmisc_1(k2_zfmisc_1(A_4682,B_4683)))
      | ~ v1_funct_1(C_4681) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_49582,plain,(
    ! [A_4682,B_4683] :
      ( v1_funct_2('#skF_4',A_4682,B_4683)
      | k1_relset_1(A_4682,B_4683,'#skF_4') != A_4682
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_49578])).

tff(c_49599,plain,(
    ! [B_4683] : v1_funct_2('#skF_4','#skF_4',B_4683) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48204,c_49582])).

tff(c_48411,plain,(
    ! [C_4560,A_4561,B_4562] :
      ( v1_funct_2(C_4560,A_4561,B_4562)
      | k1_relset_1(A_4561,B_4562,C_4560) != A_4561
      | ~ m1_subset_1(C_4560,k1_zfmisc_1(k2_zfmisc_1(A_4561,B_4562)))
      | ~ v1_funct_1(C_4560) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48415,plain,(
    ! [A_4561,B_4562] :
      ( v1_funct_2('#skF_4',A_4561,B_4562)
      | k1_relset_1(A_4561,B_4562,'#skF_4') != A_4561
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_48411])).

tff(c_48459,plain,(
    ! [B_4562] : v1_funct_2('#skF_4','#skF_4',B_4562) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48204,c_48415])).

tff(c_47955,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47940,c_64])).

tff(c_47963,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_47683,c_47683,c_47955])).

tff(c_40386,plain,(
    ! [B_10] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_xboole_0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40375,c_22])).

tff(c_40393,plain,(
    ! [B_10] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_40386])).

tff(c_47679,plain,(
    ! [B_10] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_40393])).

tff(c_47974,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_47963,c_47679])).

tff(c_47987,plain,(
    u1_pre_topc('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_47974,c_47677])).

tff(c_47740,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_108])).

tff(c_47942,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47940,c_47740])).

tff(c_48079,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47987,c_47942])).

tff(c_48054,plain,(
    ! [A_4507] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_4507),u1_pre_topc(A_4507)))
      | ~ l1_pre_topc(A_4507)
      | ~ v2_pre_topc(A_4507) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_48060,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_47940,c_48054])).

tff(c_48064,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_47987,c_48060])).

tff(c_40359,plain,(
    ! [A_3824,B_3825] :
      ( l1_pre_topc(g1_pre_topc(A_3824,B_3825))
      | ~ m1_subset_1(B_3825,k1_zfmisc_1(k1_zfmisc_1(A_3824))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_40369,plain,(
    ! [A_3824] : l1_pre_topc(g1_pre_topc(A_3824,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_20,c_40359])).

tff(c_47681,plain,(
    ! [A_3824] : l1_pre_topc(g1_pre_topc(A_3824,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_40369])).

tff(c_47944,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47940,c_82])).

tff(c_47992,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47987,c_47944])).

tff(c_48307,plain,(
    ! [B_4551,C_4552,A_4553] :
      ( B_4551 = '#skF_4'
      | v1_partfun1(C_4552,A_4553)
      | ~ v1_funct_2(C_4552,A_4553,B_4551)
      | ~ m1_subset_1(C_4552,k1_zfmisc_1(k2_zfmisc_1(A_4553,B_4551)))
      | ~ v1_funct_1(C_4552) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_58])).

tff(c_48311,plain,(
    ! [B_4551,A_4553] :
      ( B_4551 = '#skF_4'
      | v1_partfun1('#skF_4',A_4553)
      | ~ v1_funct_2('#skF_4',A_4553,B_4551)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_48307])).

tff(c_48329,plain,(
    ! [B_4554,A_4555] :
      ( B_4554 = '#skF_4'
      | v1_partfun1('#skF_4',A_4555)
      | ~ v1_funct_2('#skF_4',A_4555,B_4554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48311])).

tff(c_48336,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_47992,c_48329])).

tff(c_48350,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_48336])).

tff(c_48205,plain,(
    ! [A_4483] :
      ( A_4483 = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_4483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48203,c_48106])).

tff(c_48355,plain,(
    u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_48350,c_48205])).

tff(c_47688,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_47676,c_10])).

tff(c_48563,plain,(
    ! [D_4575,A_4576,B_4577] :
      ( v5_pre_topc(D_4575,A_4576,B_4577)
      | ~ v5_pre_topc(D_4575,A_4576,g1_pre_topc(u1_struct_0(B_4577),u1_pre_topc(B_4577)))
      | ~ m1_subset_1(D_4575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4576),u1_struct_0(g1_pre_topc(u1_struct_0(B_4577),u1_pre_topc(B_4577))))))
      | ~ v1_funct_2(D_4575,u1_struct_0(A_4576),u1_struct_0(g1_pre_topc(u1_struct_0(B_4577),u1_pre_topc(B_4577))))
      | ~ m1_subset_1(D_4575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4576),u1_struct_0(B_4577))))
      | ~ v1_funct_2(D_4575,u1_struct_0(A_4576),u1_struct_0(B_4577))
      | ~ v1_funct_1(D_4575)
      | ~ l1_pre_topc(B_4577)
      | ~ v2_pre_topc(B_4577)
      | ~ l1_pre_topc(A_4576)
      | ~ v2_pre_topc(A_4576) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_48569,plain,(
    ! [D_4575,B_4577] :
      ( v5_pre_topc(D_4575,g1_pre_topc('#skF_4','#skF_4'),B_4577)
      | ~ v5_pre_topc(D_4575,g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0(B_4577),u1_pre_topc(B_4577)))
      | ~ m1_subset_1(D_4575,k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_4577),u1_pre_topc(B_4577))))))
      | ~ v1_funct_2(D_4575,u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(g1_pre_topc(u1_struct_0(B_4577),u1_pre_topc(B_4577))))
      | ~ m1_subset_1(D_4575,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(B_4577))))
      | ~ v1_funct_2(D_4575,u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(B_4577))
      | ~ v1_funct_1(D_4575)
      | ~ l1_pre_topc(B_4577)
      | ~ v2_pre_topc(B_4577)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48355,c_48563])).

tff(c_49494,plain,(
    ! [D_4678,B_4679] :
      ( v5_pre_topc(D_4678,g1_pre_topc('#skF_4','#skF_4'),B_4679)
      | ~ v5_pre_topc(D_4678,g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0(B_4679),u1_pre_topc(B_4679)))
      | ~ v1_funct_2(D_4678,'#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_4679),u1_pre_topc(B_4679))))
      | ~ m1_subset_1(D_4678,'#skF_4')
      | ~ v1_funct_2(D_4678,'#skF_4',u1_struct_0(B_4679))
      | ~ v1_funct_1(D_4678)
      | ~ l1_pre_topc(B_4679)
      | ~ v2_pre_topc(B_4679) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48064,c_47681,c_48355,c_47683,c_47688,c_48355,c_48355,c_47683,c_47688,c_48569])).

tff(c_49507,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),'#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48079,c_49494])).

tff(c_49521,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_48459,c_47682,c_48459,c_49507])).

tff(c_48736,plain,(
    ! [D_4591,A_4592,B_4593] :
      ( v5_pre_topc(D_4591,A_4592,B_4593)
      | ~ v5_pre_topc(D_4591,g1_pre_topc(u1_struct_0(A_4592),u1_pre_topc(A_4592)),B_4593)
      | ~ m1_subset_1(D_4591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4592),u1_pre_topc(A_4592))),u1_struct_0(B_4593))))
      | ~ v1_funct_2(D_4591,u1_struct_0(g1_pre_topc(u1_struct_0(A_4592),u1_pre_topc(A_4592))),u1_struct_0(B_4593))
      | ~ m1_subset_1(D_4591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4592),u1_struct_0(B_4593))))
      | ~ v1_funct_2(D_4591,u1_struct_0(A_4592),u1_struct_0(B_4593))
      | ~ v1_funct_1(D_4591)
      | ~ l1_pre_topc(B_4593)
      | ~ v2_pre_topc(B_4593)
      | ~ l1_pre_topc(A_4592)
      | ~ v2_pre_topc(A_4592) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_48748,plain,(
    ! [D_4591,B_4593] :
      ( v5_pre_topc(D_4591,'#skF_1',B_4593)
      | ~ v5_pre_topc(D_4591,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_4593)
      | ~ m1_subset_1(D_4591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),'#skF_4')),u1_struct_0(B_4593))))
      | ~ v1_funct_2(D_4591,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_4593))
      | ~ m1_subset_1(D_4591,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_4593))))
      | ~ v1_funct_2(D_4591,u1_struct_0('#skF_1'),u1_struct_0(B_4593))
      | ~ v1_funct_1(D_4591)
      | ~ l1_pre_topc(B_4593)
      | ~ v2_pre_topc(B_4593)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47987,c_48736])).

tff(c_48770,plain,(
    ! [D_4591,B_4593] :
      ( v5_pre_topc(D_4591,'#skF_1',B_4593)
      | ~ v5_pre_topc(D_4591,g1_pre_topc('#skF_4','#skF_4'),B_4593)
      | ~ m1_subset_1(D_4591,'#skF_4')
      | ~ v1_funct_2(D_4591,'#skF_4',u1_struct_0(B_4593))
      | ~ v1_funct_1(D_4591)
      | ~ l1_pre_topc(B_4593)
      | ~ v2_pre_topc(B_4593) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_47940,c_47683,c_47688,c_47940,c_48355,c_47987,c_47940,c_47683,c_47688,c_48355,c_47940,c_47987,c_47940,c_48748])).

tff(c_49528,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_49521,c_48770])).

tff(c_49531,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_48459,c_47682,c_49528])).

tff(c_49533,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_49531])).

tff(c_49534,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48336])).

tff(c_49550,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_49534,c_40433])).

tff(c_49728,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_49550])).

tff(c_49739,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40433,c_49728])).

tff(c_49743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_49739])).

tff(c_49745,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_49550])).

tff(c_50048,plain,(
    ! [D_4730,A_4731,B_4732] :
      ( v5_pre_topc(D_4730,g1_pre_topc(u1_struct_0(A_4731),u1_pre_topc(A_4731)),B_4732)
      | ~ v5_pre_topc(D_4730,A_4731,B_4732)
      | ~ m1_subset_1(D_4730,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4731),u1_pre_topc(A_4731))),u1_struct_0(B_4732))))
      | ~ v1_funct_2(D_4730,u1_struct_0(g1_pre_topc(u1_struct_0(A_4731),u1_pre_topc(A_4731))),u1_struct_0(B_4732))
      | ~ m1_subset_1(D_4730,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4731),u1_struct_0(B_4732))))
      | ~ v1_funct_2(D_4730,u1_struct_0(A_4731),u1_struct_0(B_4732))
      | ~ v1_funct_1(D_4730)
      | ~ l1_pre_topc(B_4732)
      | ~ v2_pre_topc(B_4732)
      | ~ l1_pre_topc(A_4731)
      | ~ v2_pre_topc(A_4731) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_50057,plain,(
    ! [D_4730,B_4732] :
      ( v5_pre_topc(D_4730,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_4732)
      | ~ v5_pre_topc(D_4730,'#skF_2',B_4732)
      | ~ m1_subset_1(D_4730,k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0(B_4732))))
      | ~ v1_funct_2(D_4730,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_4732))
      | ~ m1_subset_1(D_4730,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_4732))))
      | ~ v1_funct_2(D_4730,u1_struct_0('#skF_2'),u1_struct_0(B_4732))
      | ~ v1_funct_1(D_4730)
      | ~ l1_pre_topc(B_4732)
      | ~ v2_pre_topc(B_4732)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49534,c_50048])).

tff(c_50467,plain,(
    ! [D_4777,B_4778] :
      ( v5_pre_topc(D_4777,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_4778)
      | ~ v5_pre_topc(D_4777,'#skF_2',B_4778)
      | ~ m1_subset_1(D_4777,'#skF_4')
      | ~ v1_funct_2(D_4777,'#skF_4',u1_struct_0(B_4778))
      | ~ m1_subset_1(D_4777,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_4778))))
      | ~ v1_funct_2(D_4777,u1_struct_0('#skF_2'),u1_struct_0(B_4778))
      | ~ v1_funct_1(D_4777)
      | ~ l1_pre_topc(B_4778)
      | ~ v2_pre_topc(B_4778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_49534,c_47683,c_47688,c_50057])).

tff(c_50477,plain,(
    ! [B_4778] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_4778)
      | ~ v5_pre_topc('#skF_4','#skF_2',B_4778)
      | ~ m1_subset_1('#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_4778))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_4778))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_4778)
      | ~ v2_pre_topc(B_4778) ) ),
    inference(resolution,[status(thm)],[c_47687,c_50467])).

tff(c_50488,plain,(
    ! [B_4778] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_4778)
      | ~ v5_pre_topc('#skF_4','#skF_2',B_4778)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_4778))
      | ~ l1_pre_topc(B_4778)
      | ~ v2_pre_topc(B_4778) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_49599,c_47682,c_50477])).

tff(c_49595,plain,(
    ! [A_4682,B_4683] :
      ( v1_funct_2('#skF_4',A_4682,B_4683)
      | A_4682 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48204,c_49582])).

tff(c_49660,plain,(
    ! [C_4693,A_4694,B_4695] :
      ( ~ v1_xboole_0(C_4693)
      | ~ v1_funct_2(C_4693,A_4694,B_4695)
      | ~ v1_funct_1(C_4693)
      | ~ m1_subset_1(C_4693,k1_zfmisc_1(k2_zfmisc_1(A_4694,B_4695)))
      | v1_xboole_0(B_4695)
      | v1_xboole_0(A_4694) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_49664,plain,(
    ! [A_4694,B_4695] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_4694,B_4695)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_4695)
      | v1_xboole_0(A_4694) ) ),
    inference(resolution,[status(thm)],[c_47687,c_49660])).

tff(c_49681,plain,(
    ! [A_4696,B_4697] :
      ( ~ v1_funct_2('#skF_4',A_4696,B_4697)
      | v1_xboole_0(B_4697)
      | v1_xboole_0(A_4696) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47664,c_49664])).

tff(c_49688,plain,(
    ! [B_4683,A_4682] :
      ( v1_xboole_0(B_4683)
      | v1_xboole_0(A_4682)
      | A_4682 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_49595,c_49681])).

tff(c_49692,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_49688])).

tff(c_47689,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_47676,c_8])).

tff(c_50181,plain,(
    ! [D_4752,A_4753,B_4754] :
      ( v5_pre_topc(D_4752,A_4753,B_4754)
      | ~ v5_pre_topc(D_4752,A_4753,g1_pre_topc(u1_struct_0(B_4754),u1_pre_topc(B_4754)))
      | ~ m1_subset_1(D_4752,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4753),u1_struct_0(g1_pre_topc(u1_struct_0(B_4754),u1_pre_topc(B_4754))))))
      | ~ v1_funct_2(D_4752,u1_struct_0(A_4753),u1_struct_0(g1_pre_topc(u1_struct_0(B_4754),u1_pre_topc(B_4754))))
      | ~ m1_subset_1(D_4752,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4753),u1_struct_0(B_4754))))
      | ~ v1_funct_2(D_4752,u1_struct_0(A_4753),u1_struct_0(B_4754))
      | ~ v1_funct_1(D_4752)
      | ~ l1_pre_topc(B_4754)
      | ~ v2_pre_topc(B_4754)
      | ~ l1_pre_topc(A_4753)
      | ~ v2_pre_topc(A_4753) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_50607,plain,(
    ! [B_4791,A_4792,B_4793] :
      ( v5_pre_topc(B_4791,A_4792,B_4793)
      | ~ v5_pre_topc(B_4791,A_4792,g1_pre_topc(u1_struct_0(B_4793),u1_pre_topc(B_4793)))
      | ~ v1_funct_2(B_4791,u1_struct_0(A_4792),u1_struct_0(g1_pre_topc(u1_struct_0(B_4793),u1_pre_topc(B_4793))))
      | ~ m1_subset_1(B_4791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792),u1_struct_0(B_4793))))
      | ~ v1_funct_2(B_4791,u1_struct_0(A_4792),u1_struct_0(B_4793))
      | ~ v1_funct_1(B_4791)
      | ~ l1_pre_topc(B_4793)
      | ~ v2_pre_topc(B_4793)
      | ~ l1_pre_topc(A_4792)
      | ~ v2_pre_topc(A_4792)
      | ~ v1_xboole_0(B_4791)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792),u1_struct_0(g1_pre_topc(u1_struct_0(B_4793),u1_pre_topc(B_4793)))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_50181])).

tff(c_50618,plain,(
    ! [B_4791,A_4792] :
      ( v5_pre_topc(B_4791,A_4792,'#skF_2')
      | ~ v5_pre_topc(B_4791,A_4792,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(B_4791,u1_struct_0(A_4792),'#skF_4')
      | ~ m1_subset_1(B_4791,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(B_4791,u1_struct_0(A_4792),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_4791)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_4792)
      | ~ v2_pre_topc(A_4792)
      | ~ v1_xboole_0(B_4791)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_49534,c_50607])).

tff(c_50680,plain,(
    ! [B_4797,A_4798] :
      ( v5_pre_topc(B_4797,A_4798,'#skF_2')
      | ~ v5_pre_topc(B_4797,A_4798,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(B_4797,u1_struct_0(A_4798),'#skF_4')
      | ~ m1_subset_1(B_4797,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4798),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(B_4797,u1_struct_0(A_4798),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_4797)
      | ~ l1_pre_topc(A_4798)
      | ~ v2_pre_topc(A_4798)
      | ~ v1_xboole_0(B_4797) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49692,c_47683,c_47689,c_49534,c_94,c_92,c_50618])).

tff(c_50690,plain,(
    ! [A_4798] :
      ( v5_pre_topc('#skF_4',A_4798,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_4798,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4798),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4798),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_4798)
      | ~ v2_pre_topc(A_4798)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_50680])).

tff(c_51117,plain,(
    ! [A_4838] :
      ( v5_pre_topc('#skF_4',A_4838,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_4838,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4838),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4838),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_4838)
      | ~ v2_pre_topc(A_4838) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49692,c_84,c_50690])).

tff(c_51121,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50488,c_51117])).

tff(c_51127,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49745,c_49534,c_49599,c_49534,c_49599,c_49534,c_51121])).

tff(c_51206,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_51127])).

tff(c_51209,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_51206])).

tff(c_51213,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_51209])).

tff(c_51215,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_51127])).

tff(c_49537,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49534,c_47992])).

tff(c_49897,plain,(
    ! [D_4717,A_4718,B_4719] :
      ( v5_pre_topc(D_4717,A_4718,B_4719)
      | ~ v5_pre_topc(D_4717,g1_pre_topc(u1_struct_0(A_4718),u1_pre_topc(A_4718)),B_4719)
      | ~ m1_subset_1(D_4717,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4718),u1_pre_topc(A_4718))),u1_struct_0(B_4719))))
      | ~ v1_funct_2(D_4717,u1_struct_0(g1_pre_topc(u1_struct_0(A_4718),u1_pre_topc(A_4718))),u1_struct_0(B_4719))
      | ~ m1_subset_1(D_4717,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4718),u1_struct_0(B_4719))))
      | ~ v1_funct_2(D_4717,u1_struct_0(A_4718),u1_struct_0(B_4719))
      | ~ v1_funct_1(D_4717)
      | ~ l1_pre_topc(B_4719)
      | ~ v2_pre_topc(B_4719)
      | ~ l1_pre_topc(A_4718)
      | ~ v2_pre_topc(A_4718) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_49919,plain,(
    ! [A_4718,B_4719] :
      ( v5_pre_topc('#skF_4',A_4718,B_4719)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_4718),u1_pre_topc(A_4718)),B_4719)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_4718),u1_pre_topc(A_4718))),u1_struct_0(B_4719))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4718),u1_struct_0(B_4719))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4718),u1_struct_0(B_4719))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_4719)
      | ~ v2_pre_topc(B_4719)
      | ~ l1_pre_topc(A_4718)
      | ~ v2_pre_topc(A_4718) ) ),
    inference(resolution,[status(thm)],[c_47687,c_49897])).

tff(c_51320,plain,(
    ! [A_4849,B_4850] :
      ( v5_pre_topc('#skF_4',A_4849,B_4850)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_4849),u1_pre_topc(A_4849)),B_4850)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_4849),u1_pre_topc(A_4849))),u1_struct_0(B_4850))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4849),u1_struct_0(B_4850))
      | ~ l1_pre_topc(B_4850)
      | ~ v2_pre_topc(B_4850)
      | ~ l1_pre_topc(A_4849)
      | ~ v2_pre_topc(A_4849) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47687,c_49919])).

tff(c_51341,plain,(
    ! [B_4850] :
      ( v5_pre_topc('#skF_4','#skF_1',B_4850)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_4850)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_4850))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_4850))
      | ~ l1_pre_topc(B_4850)
      | ~ v2_pre_topc(B_4850)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47940,c_51320])).

tff(c_51360,plain,(
    ! [B_4851] :
      ( v5_pre_topc('#skF_4','#skF_1',B_4851)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),B_4851)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(B_4851))
      | ~ l1_pre_topc(B_4851)
      | ~ v2_pre_topc(B_4851) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_49599,c_47940,c_47987,c_47940,c_47987,c_51341])).

tff(c_51366,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_49534,c_51360])).

tff(c_51372,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51215,c_49745,c_49537,c_48079,c_51366])).

tff(c_50701,plain,(
    ! [A_4798] :
      ( v5_pre_topc('#skF_4',A_4798,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_4798,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4798),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_4798),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_4798)
      | ~ v2_pre_topc(A_4798) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49692,c_84,c_50690])).

tff(c_51378,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51372,c_50701])).

tff(c_51381,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_49599,c_47940,c_49599,c_47940,c_51378])).

tff(c_51383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_51381])).

tff(c_51384,plain,(
    ! [B_4683] : v1_xboole_0(B_4683) ),
    inference(splitRight,[status(thm)],[c_49688])).

tff(c_51436,plain,(
    ! [A_4853] : A_4853 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51384,c_47677])).

tff(c_49601,plain,(
    ! [A_4684,B_4685] :
      ( v1_funct_2('#skF_4',A_4684,B_4685)
      | A_4684 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48204,c_49582])).

tff(c_48324,plain,(
    ! [B_4551,A_4553] :
      ( B_4551 = '#skF_4'
      | v1_partfun1('#skF_4',A_4553)
      | ~ v1_funct_2('#skF_4',A_4553,B_4551) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_48311])).

tff(c_49612,plain,(
    ! [B_4685,A_4684] :
      ( B_4685 = '#skF_4'
      | v1_partfun1('#skF_4',A_4684)
      | A_4684 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_49601,c_48324])).

tff(c_49620,plain,(
    ! [A_4686] :
      ( v1_partfun1('#skF_4',A_4686)
      | A_4686 != '#skF_4' ) ),
    inference(splitLeft,[status(thm)],[c_49612])).

tff(c_49535,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_48336])).

tff(c_49627,plain,(
    u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_49620,c_49535])).

tff(c_51557,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_51436,c_49627])).

tff(c_51559,plain,(
    ! [B_5424] : B_5424 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_49612])).

tff(c_51574,plain,(
    ~ v1_partfun1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_51559,c_49535])).

tff(c_51712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48199,c_51574])).

tff(c_51713,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_47935])).

tff(c_51717,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51713,c_107])).

tff(c_51911,plain,(
    ! [A_6208,B_6209,C_6210] :
      ( k1_relset_1(A_6208,B_6209,C_6210) = k1_relat_1(C_6210)
      | ~ m1_subset_1(C_6210,k1_zfmisc_1(k2_zfmisc_1(A_6208,B_6209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_51926,plain,(
    ! [A_6208,B_6209] : k1_relset_1(A_6208,B_6209,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_47687,c_51911])).

tff(c_52053,plain,(
    ! [C_6238,A_6239,B_6240] :
      ( v1_funct_2(C_6238,A_6239,B_6240)
      | k1_relset_1(A_6239,B_6240,C_6238) != A_6239
      | ~ m1_subset_1(C_6238,k1_zfmisc_1(k2_zfmisc_1(A_6239,B_6240)))
      | ~ v1_funct_1(C_6238) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52057,plain,(
    ! [A_6239,B_6240] :
      ( v1_funct_2('#skF_4',A_6239,B_6240)
      | k1_relset_1(A_6239,B_6240,'#skF_4') != A_6239
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_52053])).

tff(c_52070,plain,(
    ! [A_6239,B_6240] :
      ( v1_funct_2('#skF_4',A_6239,B_6240)
      | k1_relat_1('#skF_4') != A_6239 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_51926,c_52057])).

tff(c_52632,plain,(
    ! [C_6862,A_6863,B_6864] :
      ( ~ v1_xboole_0(C_6862)
      | ~ v1_funct_2(C_6862,A_6863,B_6864)
      | ~ v1_funct_1(C_6862)
      | ~ m1_subset_1(C_6862,k1_zfmisc_1(k2_zfmisc_1(A_6863,B_6864)))
      | v1_xboole_0(B_6864)
      | v1_xboole_0(A_6863) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52636,plain,(
    ! [A_6863,B_6864] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_6863,B_6864)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_6864)
      | v1_xboole_0(A_6863) ) ),
    inference(resolution,[status(thm)],[c_47687,c_52632])).

tff(c_52666,plain,(
    ! [A_6866,B_6867] :
      ( ~ v1_funct_2('#skF_4',A_6866,B_6867)
      | v1_xboole_0(B_6867)
      | v1_xboole_0(A_6866) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47664,c_52636])).

tff(c_52678,plain,(
    ! [B_6240,A_6239] :
      ( v1_xboole_0(B_6240)
      | v1_xboole_0(A_6239)
      | k1_relat_1('#skF_4') != A_6239 ) ),
    inference(resolution,[status(thm)],[c_52070,c_52666])).

tff(c_52687,plain,(
    ! [A_6868] :
      ( v1_xboole_0(A_6868)
      | k1_relat_1('#skF_4') != A_6868 ) ),
    inference(splitLeft,[status(thm)],[c_52678])).

tff(c_52723,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52687,c_47677])).

tff(c_52075,plain,(
    ! [A_6241,B_6242] :
      ( v1_funct_2('#skF_4',A_6241,B_6242)
      | k1_relat_1('#skF_4') != A_6241 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_51926,c_52057])).

tff(c_51972,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,'#skF_4')
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47683,c_47676,c_47676,c_47676,c_113])).

tff(c_52082,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_52075,c_51972])).

tff(c_52086,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47682,c_52082])).

tff(c_52087,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_52086])).

tff(c_52732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52723,c_52087])).

tff(c_52733,plain,(
    ! [B_6240] : v1_xboole_0(B_6240) ),
    inference(splitRight,[status(thm)],[c_52678])).

tff(c_52781,plain,(
    ! [A_6871] : A_6871 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52733,c_47677])).

tff(c_52911,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_52781,c_52087])).

tff(c_52913,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52086])).

tff(c_52945,plain,(
    ! [A_6239,B_6240] :
      ( v1_funct_2('#skF_4',A_6239,B_6240)
      | A_6239 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52913,c_52070])).

tff(c_53013,plain,(
    ! [C_7441,A_7442,B_7443] :
      ( ~ v1_xboole_0(C_7441)
      | ~ v1_funct_2(C_7441,A_7442,B_7443)
      | ~ v1_funct_1(C_7441)
      | ~ m1_subset_1(C_7441,k1_zfmisc_1(k2_zfmisc_1(A_7442,B_7443)))
      | v1_xboole_0(B_7443)
      | v1_xboole_0(A_7442) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_53017,plain,(
    ! [A_7442,B_7443] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_7442,B_7443)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_7443)
      | v1_xboole_0(A_7442) ) ),
    inference(resolution,[status(thm)],[c_47687,c_53013])).

tff(c_53047,plain,(
    ! [A_7445,B_7446] :
      ( ~ v1_funct_2('#skF_4',A_7445,B_7446)
      | v1_xboole_0(B_7446)
      | v1_xboole_0(A_7445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47664,c_53017])).

tff(c_53057,plain,(
    ! [B_6240,A_6239] :
      ( v1_xboole_0(B_6240)
      | v1_xboole_0(A_6239)
      | A_6239 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_52945,c_53047])).

tff(c_53061,plain,(
    ! [A_6239] :
      ( v1_xboole_0(A_6239)
      | A_6239 != '#skF_4' ) ),
    inference(splitLeft,[status(thm)],[c_53057])).

tff(c_53063,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_53057])).

tff(c_52999,plain,(
    ! [B_6240] : v1_funct_2('#skF_4','#skF_4',B_6240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52913,c_52070])).

tff(c_51729,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_51713,c_64])).

tff(c_51737,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_47683,c_47683,c_51729])).

tff(c_51769,plain,(
    v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_51737,c_47679])).

tff(c_51782,plain,(
    u1_pre_topc('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_51769,c_47677])).

tff(c_51716,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51713,c_47740])).

tff(c_51854,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51782,c_51716])).

tff(c_51718,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51713,c_82])).

tff(c_51786,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51782,c_51718])).

tff(c_53058,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_51786,c_53047])).

tff(c_53062,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_53058])).

tff(c_53129,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_53062,c_47677])).

tff(c_47697,plain,(
    ! [A_4468,B_4469] :
      ( v1_pre_topc(g1_pre_topc(A_4468,B_4469))
      | ~ m1_subset_1(B_4469,k1_zfmisc_1(k1_zfmisc_1(A_4468))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_47705,plain,(
    ! [A_45] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_47697])).

tff(c_53190,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53129,c_47705])).

tff(c_53576,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_53190])).

tff(c_53582,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40433,c_53576])).

tff(c_53587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_53582])).

tff(c_53589,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_53190])).

tff(c_53304,plain,(
    ! [D_7464,A_7465,B_7466] :
      ( v5_pre_topc(D_7464,A_7465,g1_pre_topc(u1_struct_0(B_7466),u1_pre_topc(B_7466)))
      | ~ v5_pre_topc(D_7464,A_7465,B_7466)
      | ~ m1_subset_1(D_7464,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7465),u1_struct_0(g1_pre_topc(u1_struct_0(B_7466),u1_pre_topc(B_7466))))))
      | ~ v1_funct_2(D_7464,u1_struct_0(A_7465),u1_struct_0(g1_pre_topc(u1_struct_0(B_7466),u1_pre_topc(B_7466))))
      | ~ m1_subset_1(D_7464,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7465),u1_struct_0(B_7466))))
      | ~ v1_funct_2(D_7464,u1_struct_0(A_7465),u1_struct_0(B_7466))
      | ~ v1_funct_1(D_7464)
      | ~ l1_pre_topc(B_7466)
      | ~ v2_pre_topc(B_7466)
      | ~ l1_pre_topc(A_7465)
      | ~ v2_pre_topc(A_7465) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_54457,plain,(
    ! [B_7578,A_7579,B_7580] :
      ( v5_pre_topc(B_7578,A_7579,g1_pre_topc(u1_struct_0(B_7580),u1_pre_topc(B_7580)))
      | ~ v5_pre_topc(B_7578,A_7579,B_7580)
      | ~ v1_funct_2(B_7578,u1_struct_0(A_7579),u1_struct_0(g1_pre_topc(u1_struct_0(B_7580),u1_pre_topc(B_7580))))
      | ~ m1_subset_1(B_7578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579),u1_struct_0(B_7580))))
      | ~ v1_funct_2(B_7578,u1_struct_0(A_7579),u1_struct_0(B_7580))
      | ~ v1_funct_1(B_7578)
      | ~ l1_pre_topc(B_7580)
      | ~ v2_pre_topc(B_7580)
      | ~ l1_pre_topc(A_7579)
      | ~ v2_pre_topc(A_7579)
      | ~ v1_xboole_0(B_7578)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579),u1_struct_0(g1_pre_topc(u1_struct_0(B_7580),u1_pre_topc(B_7580)))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_53304])).

tff(c_54465,plain,(
    ! [B_7578,A_7579] :
      ( v5_pre_topc(B_7578,A_7579,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v5_pre_topc(B_7578,A_7579,'#skF_1')
      | ~ v1_funct_2(B_7578,u1_struct_0(A_7579),'#skF_4')
      | ~ m1_subset_1(B_7578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(B_7578,u1_struct_0(A_7579),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(B_7578)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ l1_pre_topc(A_7579)
      | ~ v2_pre_topc(A_7579)
      | ~ v1_xboole_0(B_7578)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53129,c_54457])).

tff(c_54535,plain,(
    ! [B_7586,A_7587] :
      ( v5_pre_topc(B_7586,A_7587,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v5_pre_topc(B_7586,A_7587,'#skF_1')
      | ~ v1_funct_2(B_7586,u1_struct_0(A_7587),'#skF_4')
      | ~ m1_subset_1(B_7586,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7587),u1_struct_0('#skF_1'))))
      | ~ v1_funct_2(B_7586,u1_struct_0(A_7587),u1_struct_0('#skF_1'))
      | ~ v1_funct_1(B_7586)
      | ~ l1_pre_topc(A_7587)
      | ~ v2_pre_topc(A_7587)
      | ~ v1_xboole_0(B_7586) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53063,c_47683,c_47689,c_53129,c_98,c_96,c_54465])).

tff(c_54545,plain,(
    ! [A_7587] :
      ( v5_pre_topc('#skF_4',A_7587,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v5_pre_topc('#skF_4',A_7587,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7587),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7587),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_7587)
      | ~ v2_pre_topc(A_7587)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_54535])).

tff(c_54558,plain,(
    ! [A_7588] :
      ( v5_pre_topc('#skF_4',A_7588,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v5_pre_topc('#skF_4',A_7588,'#skF_1')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7588),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7588),u1_struct_0('#skF_1'))
      | ~ l1_pre_topc(A_7588)
      | ~ v2_pre_topc(A_7588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53063,c_84,c_54545])).

tff(c_53397,plain,(
    ! [D_7478,A_7479,B_7480] :
      ( v5_pre_topc(D_7478,A_7479,B_7480)
      | ~ v5_pre_topc(D_7478,g1_pre_topc(u1_struct_0(A_7479),u1_pre_topc(A_7479)),B_7480)
      | ~ m1_subset_1(D_7478,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_7479),u1_pre_topc(A_7479))),u1_struct_0(B_7480))))
      | ~ v1_funct_2(D_7478,u1_struct_0(g1_pre_topc(u1_struct_0(A_7479),u1_pre_topc(A_7479))),u1_struct_0(B_7480))
      | ~ m1_subset_1(D_7478,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7479),u1_struct_0(B_7480))))
      | ~ v1_funct_2(D_7478,u1_struct_0(A_7479),u1_struct_0(B_7480))
      | ~ v1_funct_1(D_7478)
      | ~ l1_pre_topc(B_7480)
      | ~ v2_pre_topc(B_7480)
      | ~ l1_pre_topc(A_7479)
      | ~ v2_pre_topc(A_7479) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_54150,plain,(
    ! [B_7553,A_7554,B_7555] :
      ( v5_pre_topc(B_7553,A_7554,B_7555)
      | ~ v5_pre_topc(B_7553,g1_pre_topc(u1_struct_0(A_7554),u1_pre_topc(A_7554)),B_7555)
      | ~ v1_funct_2(B_7553,u1_struct_0(g1_pre_topc(u1_struct_0(A_7554),u1_pre_topc(A_7554))),u1_struct_0(B_7555))
      | ~ m1_subset_1(B_7553,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7554),u1_struct_0(B_7555))))
      | ~ v1_funct_2(B_7553,u1_struct_0(A_7554),u1_struct_0(B_7555))
      | ~ v1_funct_1(B_7553)
      | ~ l1_pre_topc(B_7555)
      | ~ v2_pre_topc(B_7555)
      | ~ l1_pre_topc(A_7554)
      | ~ v2_pre_topc(A_7554)
      | ~ v1_xboole_0(B_7553)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_7554),u1_pre_topc(A_7554))),u1_struct_0(B_7555)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_53397])).

tff(c_54156,plain,(
    ! [B_7553,B_7555] :
      ( v5_pre_topc(B_7553,'#skF_1',B_7555)
      | ~ v5_pre_topc(B_7553,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7555)
      | ~ v1_funct_2(B_7553,'#skF_4',u1_struct_0(B_7555))
      | ~ m1_subset_1(B_7553,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_7555))))
      | ~ v1_funct_2(B_7553,u1_struct_0('#skF_1'),u1_struct_0(B_7555))
      | ~ v1_funct_1(B_7553)
      | ~ l1_pre_topc(B_7555)
      | ~ v2_pre_topc(B_7555)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ v1_xboole_0(B_7553)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_7555)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53129,c_54150])).

tff(c_54295,plain,(
    ! [B_7565,B_7566] :
      ( v5_pre_topc(B_7565,'#skF_1',B_7566)
      | ~ v5_pre_topc(B_7565,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7566)
      | ~ v1_funct_2(B_7565,'#skF_4',u1_struct_0(B_7566))
      | ~ m1_subset_1(B_7565,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_7566))))
      | ~ v1_funct_2(B_7565,u1_struct_0('#skF_1'),u1_struct_0(B_7566))
      | ~ v1_funct_1(B_7565)
      | ~ l1_pre_topc(B_7566)
      | ~ v2_pre_topc(B_7566)
      | ~ v1_xboole_0(B_7565) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53063,c_47683,c_47688,c_53129,c_98,c_96,c_54156])).

tff(c_54305,plain,(
    ! [B_7566] :
      ( v5_pre_topc('#skF_4','#skF_1',B_7566)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7566)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_7566))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_7566))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_7566)
      | ~ v2_pre_topc(B_7566)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_54295])).

tff(c_54316,plain,(
    ! [B_7566] :
      ( v5_pre_topc('#skF_4','#skF_1',B_7566)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7566)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_7566))
      | ~ l1_pre_topc(B_7566)
      | ~ v2_pre_topc(B_7566) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53063,c_84,c_52999,c_54305])).

tff(c_54562,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0('#skF_1'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_54558,c_54316])).

tff(c_54565,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_1')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53589,c_52999,c_53129,c_52999,c_53129,c_51717,c_53129,c_54562])).

tff(c_54566,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_54565])).

tff(c_54569,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_54566])).

tff(c_54573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_54569])).

tff(c_54575,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54565])).

tff(c_53132,plain,(
    ! [D_7453,A_7454,B_7455] :
      ( v5_pre_topc(D_7453,A_7454,B_7455)
      | ~ v5_pre_topc(D_7453,A_7454,g1_pre_topc(u1_struct_0(B_7455),u1_pre_topc(B_7455)))
      | ~ m1_subset_1(D_7453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7454),u1_struct_0(g1_pre_topc(u1_struct_0(B_7455),u1_pre_topc(B_7455))))))
      | ~ v1_funct_2(D_7453,u1_struct_0(A_7454),u1_struct_0(g1_pre_topc(u1_struct_0(B_7455),u1_pre_topc(B_7455))))
      | ~ m1_subset_1(D_7453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7454),u1_struct_0(B_7455))))
      | ~ v1_funct_2(D_7453,u1_struct_0(A_7454),u1_struct_0(B_7455))
      | ~ v1_funct_1(D_7453)
      | ~ l1_pre_topc(B_7455)
      | ~ v2_pre_topc(B_7455)
      | ~ l1_pre_topc(A_7454)
      | ~ v2_pre_topc(A_7454) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_53145,plain,(
    ! [A_7454,B_7455] :
      ( v5_pre_topc('#skF_4',A_7454,B_7455)
      | ~ v5_pre_topc('#skF_4',A_7454,g1_pre_topc(u1_struct_0(B_7455),u1_pre_topc(B_7455)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7454),u1_struct_0(g1_pre_topc(u1_struct_0(B_7455),u1_pre_topc(B_7455))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7454),u1_struct_0(B_7455))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7454),u1_struct_0(B_7455))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_7455)
      | ~ v2_pre_topc(B_7455)
      | ~ l1_pre_topc(A_7454)
      | ~ v2_pre_topc(A_7454) ) ),
    inference(resolution,[status(thm)],[c_47687,c_53132])).

tff(c_54728,plain,(
    ! [A_7599,B_7600] :
      ( v5_pre_topc('#skF_4',A_7599,B_7600)
      | ~ v5_pre_topc('#skF_4',A_7599,g1_pre_topc(u1_struct_0(B_7600),u1_pre_topc(B_7600)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7599),u1_struct_0(g1_pre_topc(u1_struct_0(B_7600),u1_pre_topc(B_7600))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_7599),u1_struct_0(B_7600))
      | ~ l1_pre_topc(B_7600)
      | ~ v2_pre_topc(B_7600)
      | ~ l1_pre_topc(A_7599)
      | ~ v2_pre_topc(A_7599) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_47687,c_53145])).

tff(c_54734,plain,(
    ! [B_7600] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7600)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_7600),u1_pre_topc(B_7600)))
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_7600),u1_pre_topc(B_7600))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_7600))
      | ~ l1_pre_topc(B_7600)
      | ~ v2_pre_topc(B_7600)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53129,c_54728])).

tff(c_54804,plain,(
    ! [B_7602] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_7602)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_7602),u1_pre_topc(B_7602)))
      | ~ l1_pre_topc(B_7602)
      | ~ v2_pre_topc(B_7602) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54575,c_53589,c_52999,c_53129,c_52999,c_54734])).

tff(c_54820,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_51782,c_54804])).

tff(c_54834,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_51854,c_51713,c_54820])).

tff(c_54301,plain,(
    ! [B_7565] :
      ( v5_pre_topc(B_7565,'#skF_1','#skF_2')
      | ~ v5_pre_topc(B_7565,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v1_funct_2(B_7565,'#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_7565,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')))
      | ~ v1_funct_2(B_7565,u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_7565)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ v1_xboole_0(B_7565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51713,c_54295])).

tff(c_54313,plain,(
    ! [B_7565] :
      ( v5_pre_topc(B_7565,'#skF_1','#skF_2')
      | ~ v5_pre_topc(B_7565,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
      | ~ v1_funct_2(B_7565,'#skF_4','#skF_4')
      | ~ m1_subset_1(B_7565,'#skF_4')
      | ~ v1_funct_2(B_7565,u1_struct_0('#skF_1'),'#skF_4')
      | ~ v1_funct_1(B_7565)
      | ~ v1_xboole_0(B_7565) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_51713,c_47683,c_47689,c_51713,c_54301])).

tff(c_54839,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_54834,c_54313])).

tff(c_54845,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53063,c_84,c_51717,c_47682,c_52999,c_54839])).

tff(c_54847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_54845])).

tff(c_54849,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_53058])).

tff(c_55098,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) != '#skF_4' ),
    inference(resolution,[status(thm)],[c_53061,c_54849])).

tff(c_51996,plain,(
    ! [B_6227,C_6228,A_6229] :
      ( B_6227 = '#skF_4'
      | v1_partfun1(C_6228,A_6229)
      | ~ v1_funct_2(C_6228,A_6229,B_6227)
      | ~ m1_subset_1(C_6228,k1_zfmisc_1(k2_zfmisc_1(A_6229,B_6227)))
      | ~ v1_funct_1(C_6228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47676,c_58])).

tff(c_52000,plain,(
    ! [B_6227,A_6229] :
      ( B_6227 = '#skF_4'
      | v1_partfun1('#skF_4',A_6229)
      | ~ v1_funct_2('#skF_4',A_6229,B_6227)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47687,c_51996])).

tff(c_52018,plain,(
    ! [B_6230,A_6231] :
      ( B_6230 = '#skF_4'
      | v1_partfun1('#skF_4',A_6231)
      | ~ v1_funct_2('#skF_4',A_6231,B_6230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_52000])).

tff(c_52025,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_51786,c_52018])).

tff(c_52970,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_52025])).

tff(c_51877,plain,(
    ! [B_6202,A_6203] :
      ( k1_relat_1(B_6202) = A_6203
      | ~ v1_partfun1(B_6202,A_6203)
      | ~ v4_relat_1(B_6202,A_6203)
      | ~ v1_relat_1(B_6202) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_51883,plain,(
    ! [A_4483] :
      ( k1_relat_1('#skF_4') = A_4483
      | ~ v1_partfun1('#skF_4',A_4483)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_47873,c_51877])).

tff(c_51887,plain,(
    ! [A_4483] :
      ( k1_relat_1('#skF_4') = A_4483
      | ~ v1_partfun1('#skF_4',A_4483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_51883])).

tff(c_52947,plain,(
    ! [A_4483] :
      ( A_4483 = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_4483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52913,c_51887])).

tff(c_55172,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52970,c_52947])).

tff(c_55179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55098,c_55172])).

tff(c_55180,plain,(
    ! [B_6240] : v1_xboole_0(B_6240) ),
    inference(splitRight,[status(thm)],[c_53057])).

tff(c_55228,plain,(
    ! [A_7621] : A_7621 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55180,c_47677])).

tff(c_51714,plain,(
    u1_struct_0('#skF_1') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_47935])).

tff(c_55358,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_55228,c_51714])).

tff(c_55359,plain,(
    u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52025])).

tff(c_55410,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55359,c_51786])).

tff(c_51841,plain,(
    ! [A_6191] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_6191),u1_pre_topc(A_6191)))
      | ~ l1_pre_topc(A_6191)
      | ~ v2_pre_topc(A_6191) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_51847,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_51713,c_51841])).

tff(c_51851,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_51782,c_51847])).

tff(c_55509,plain,(
    ! [D_8158,A_8159,B_8160] :
      ( v5_pre_topc(D_8158,A_8159,B_8160)
      | ~ v5_pre_topc(D_8158,g1_pre_topc(u1_struct_0(A_8159),u1_pre_topc(A_8159)),B_8160)
      | ~ m1_subset_1(D_8158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_8159),u1_pre_topc(A_8159))),u1_struct_0(B_8160))))
      | ~ v1_funct_2(D_8158,u1_struct_0(g1_pre_topc(u1_struct_0(A_8159),u1_pre_topc(A_8159))),u1_struct_0(B_8160))
      | ~ m1_subset_1(D_8158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8159),u1_struct_0(B_8160))))
      | ~ v1_funct_2(D_8158,u1_struct_0(A_8159),u1_struct_0(B_8160))
      | ~ v1_funct_1(D_8158)
      | ~ l1_pre_topc(B_8160)
      | ~ v2_pre_topc(B_8160)
      | ~ l1_pre_topc(A_8159)
      | ~ v2_pre_topc(A_8159) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_55518,plain,(
    ! [D_8158,A_8159] :
      ( v5_pre_topc(D_8158,A_8159,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_8158,g1_pre_topc(u1_struct_0(A_8159),u1_pre_topc(A_8159)),g1_pre_topc('#skF_4','#skF_4'))
      | ~ m1_subset_1(D_8158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_8159),u1_pre_topc(A_8159))),'#skF_4')))
      | ~ v1_funct_2(D_8158,u1_struct_0(g1_pre_topc(u1_struct_0(A_8159),u1_pre_topc(A_8159))),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
      | ~ m1_subset_1(D_8158,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8159),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))))
      | ~ v1_funct_2(D_8158,u1_struct_0(A_8159),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
      | ~ v1_funct_1(D_8158)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ l1_pre_topc(A_8159)
      | ~ v2_pre_topc(A_8159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55359,c_55509])).

tff(c_55869,plain,(
    ! [D_8187,A_8188] :
      ( v5_pre_topc(D_8187,A_8188,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_8187,g1_pre_topc(u1_struct_0(A_8188),u1_pre_topc(A_8188)),g1_pre_topc('#skF_4','#skF_4'))
      | ~ v1_funct_2(D_8187,u1_struct_0(g1_pre_topc(u1_struct_0(A_8188),u1_pre_topc(A_8188))),'#skF_4')
      | ~ m1_subset_1(D_8187,'#skF_4')
      | ~ v1_funct_2(D_8187,u1_struct_0(A_8188),'#skF_4')
      | ~ v1_funct_1(D_8187)
      | ~ l1_pre_topc(A_8188)
      | ~ v2_pre_topc(A_8188) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51851,c_47681,c_55359,c_47683,c_47689,c_55359,c_55359,c_47683,c_47689,c_55518])).

tff(c_55878,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_51854,c_55869])).

tff(c_55891,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_51717,c_47682,c_55410,c_55878])).

tff(c_55589,plain,(
    ! [D_8164,A_8165,B_8166] :
      ( v5_pre_topc(D_8164,A_8165,B_8166)
      | ~ v5_pre_topc(D_8164,A_8165,g1_pre_topc(u1_struct_0(B_8166),u1_pre_topc(B_8166)))
      | ~ m1_subset_1(D_8164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165),u1_struct_0(g1_pre_topc(u1_struct_0(B_8166),u1_pre_topc(B_8166))))))
      | ~ v1_funct_2(D_8164,u1_struct_0(A_8165),u1_struct_0(g1_pre_topc(u1_struct_0(B_8166),u1_pre_topc(B_8166))))
      | ~ m1_subset_1(D_8164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165),u1_struct_0(B_8166))))
      | ~ v1_funct_2(D_8164,u1_struct_0(A_8165),u1_struct_0(B_8166))
      | ~ v1_funct_1(D_8164)
      | ~ l1_pre_topc(B_8166)
      | ~ v2_pre_topc(B_8166)
      | ~ l1_pre_topc(A_8165)
      | ~ v2_pre_topc(A_8165) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_55601,plain,(
    ! [D_8164,A_8165] :
      ( v5_pre_topc(D_8164,A_8165,'#skF_2')
      | ~ v5_pre_topc(D_8164,A_8165,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_subset_1(D_8164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),'#skF_4')))))
      | ~ v1_funct_2(D_8164,u1_struct_0(A_8165),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_8164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_8164,u1_struct_0(A_8165),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_8164)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_8165)
      | ~ v2_pre_topc(A_8165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_51782,c_55589])).

tff(c_56898,plain,(
    ! [D_8301,A_8302] :
      ( v5_pre_topc(D_8301,A_8302,'#skF_2')
      | ~ v5_pre_topc(D_8301,A_8302,g1_pre_topc('#skF_4','#skF_4'))
      | ~ m1_subset_1(D_8301,'#skF_4')
      | ~ v1_funct_2(D_8301,u1_struct_0(A_8302),'#skF_4')
      | ~ v1_funct_1(D_8301)
      | ~ l1_pre_topc(A_8302)
      | ~ v2_pre_topc(A_8302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_51713,c_47683,c_47689,c_51713,c_55359,c_51713,c_51782,c_47683,c_47689,c_55359,c_51713,c_51713,c_51782,c_55601])).

tff(c_56910,plain,
    ( v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_55891,c_56898])).

tff(c_56923,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_51717,c_47682,c_56910])).

tff(c_56925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40401,c_56923])).

tff(c_56927,plain,(
    v5_pre_topc('#skF_4','#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_57030,plain,(
    ! [C_8321,A_8322,B_8323] :
      ( v4_relat_1(C_8321,A_8322)
      | ~ m1_subset_1(C_8321,k1_zfmisc_1(k2_zfmisc_1(A_8322,B_8323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_57052,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_111,c_57030])).

tff(c_57137,plain,(
    ! [B_8340,A_8341] :
      ( k1_relat_1(B_8340) = A_8341
      | ~ v1_partfun1(B_8340,A_8341)
      | ~ v4_relat_1(B_8340,A_8341)
      | ~ v1_relat_1(B_8340) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_57146,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_57052,c_57137])).

tff(c_57156,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_57146])).

tff(c_57166,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_57156])).

tff(c_57465,plain,(
    ! [B_8415,C_8416,A_8417] :
      ( k1_xboole_0 = B_8415
      | v1_partfun1(C_8416,A_8417)
      | ~ v1_funct_2(C_8416,A_8417,B_8415)
      | ~ m1_subset_1(C_8416,k1_zfmisc_1(k2_zfmisc_1(A_8417,B_8415)))
      | ~ v1_funct_1(C_8416) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_57471,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_111,c_57465])).

tff(c_57491,plain,
    ( u1_struct_0('#skF_2') = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_57471])).

tff(c_57492,plain,(
    u1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_57166,c_57491])).

tff(c_57063,plain,(
    ! [C_8329,B_8330,A_8331] :
      ( v1_xboole_0(C_8329)
      | ~ m1_subset_1(C_8329,k1_zfmisc_1(k2_zfmisc_1(B_8330,A_8331)))
      | ~ v1_xboole_0(A_8331) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_57085,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_111,c_57063])).

tff(c_57111,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_57085])).

tff(c_57506,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57492,c_57111])).

tff(c_57518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_57506])).

tff(c_57519,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_57156])).

tff(c_56926,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_57572,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57519,c_56926])).

tff(c_57084,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_80,c_57063])).

tff(c_57118,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_57084])).

tff(c_57528,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57519,c_82])).

tff(c_57525,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57519,c_80])).

tff(c_57785,plain,(
    ! [C_8443,A_8444,B_8445] :
      ( v1_partfun1(C_8443,A_8444)
      | ~ v1_funct_2(C_8443,A_8444,B_8445)
      | ~ v1_funct_1(C_8443)
      | ~ m1_subset_1(C_8443,k1_zfmisc_1(k2_zfmisc_1(A_8444,B_8445)))
      | v1_xboole_0(B_8445) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_57791,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_57525,c_57785])).

tff(c_57812,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_57528,c_57791])).

tff(c_57813,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')))) ),
    inference(negUnitSimplification,[status(thm)],[c_57118,c_57812])).

tff(c_57051,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_80,c_57030])).

tff(c_57140,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_57051,c_57137])).

tff(c_57152,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_57140])).

tff(c_58185,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57813,c_57519,c_57519,c_57152])).

tff(c_58193,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58185,c_57528])).

tff(c_58192,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58185,c_57525])).

tff(c_59376,plain,(
    ! [D_8582,A_8583,B_8584] :
      ( v5_pre_topc(D_8582,g1_pre_topc(u1_struct_0(A_8583),u1_pre_topc(A_8583)),B_8584)
      | ~ v5_pre_topc(D_8582,A_8583,B_8584)
      | ~ m1_subset_1(D_8582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_8583),u1_pre_topc(A_8583))),u1_struct_0(B_8584))))
      | ~ v1_funct_2(D_8582,u1_struct_0(g1_pre_topc(u1_struct_0(A_8583),u1_pre_topc(A_8583))),u1_struct_0(B_8584))
      | ~ m1_subset_1(D_8582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8583),u1_struct_0(B_8584))))
      | ~ v1_funct_2(D_8582,u1_struct_0(A_8583),u1_struct_0(B_8584))
      | ~ v1_funct_1(D_8582)
      | ~ l1_pre_topc(B_8584)
      | ~ v2_pre_topc(B_8584)
      | ~ l1_pre_topc(A_8583)
      | ~ v2_pre_topc(A_8583) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_59385,plain,(
    ! [D_8582,B_8584] :
      ( v5_pre_topc(D_8582,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_8584)
      | ~ v5_pre_topc(D_8582,'#skF_1',B_8584)
      | ~ m1_subset_1(D_8582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1'))),u1_struct_0(B_8584))))
      | ~ v1_funct_2(D_8582,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_8584))
      | ~ m1_subset_1(D_8582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_8584))))
      | ~ v1_funct_2(D_8582,u1_struct_0('#skF_1'),u1_struct_0(B_8584))
      | ~ v1_funct_1(D_8582)
      | ~ l1_pre_topc(B_8584)
      | ~ v2_pre_topc(B_8584)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57519,c_59376])).

tff(c_60088,plain,(
    ! [D_8650,B_8651] :
      ( v5_pre_topc(D_8650,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),B_8651)
      | ~ v5_pre_topc(D_8650,'#skF_1',B_8651)
      | ~ m1_subset_1(D_8650,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_8651))))
      | ~ v1_funct_2(D_8650,k1_relat_1('#skF_4'),u1_struct_0(B_8651))
      | ~ v1_funct_1(D_8650)
      | ~ l1_pre_topc(B_8651)
      | ~ v2_pre_topc(B_8651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_57519,c_57519,c_58185,c_57519,c_58185,c_57519,c_59385])).

tff(c_60091,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_58192,c_60088])).

tff(c_60111,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_58193,c_60091])).

tff(c_60112,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_57572,c_60111])).

tff(c_60122,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_60112])).

tff(c_60125,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_60122])).

tff(c_60129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_60125])).

tff(c_60130,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60112])).

tff(c_60132,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_60130])).

tff(c_57527,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57519,c_107])).

tff(c_57526,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57519,c_111])).

tff(c_58249,plain,(
    ! [D_8508,A_8509,B_8510] :
      ( v5_pre_topc(D_8508,A_8509,g1_pre_topc(u1_struct_0(B_8510),u1_pre_topc(B_8510)))
      | ~ v5_pre_topc(D_8508,A_8509,B_8510)
      | ~ m1_subset_1(D_8508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8509),u1_struct_0(g1_pre_topc(u1_struct_0(B_8510),u1_pre_topc(B_8510))))))
      | ~ v1_funct_2(D_8508,u1_struct_0(A_8509),u1_struct_0(g1_pre_topc(u1_struct_0(B_8510),u1_pre_topc(B_8510))))
      | ~ m1_subset_1(D_8508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8509),u1_struct_0(B_8510))))
      | ~ v1_funct_2(D_8508,u1_struct_0(A_8509),u1_struct_0(B_8510))
      | ~ v1_funct_1(D_8508)
      | ~ l1_pre_topc(B_8510)
      | ~ v2_pre_topc(B_8510)
      | ~ l1_pre_topc(A_8509)
      | ~ v2_pre_topc(A_8509) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_58258,plain,(
    ! [D_8508,B_8510] :
      ( v5_pre_topc(D_8508,'#skF_1',g1_pre_topc(u1_struct_0(B_8510),u1_pre_topc(B_8510)))
      | ~ v5_pre_topc(D_8508,'#skF_1',B_8510)
      | ~ m1_subset_1(D_8508,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_8510),u1_pre_topc(B_8510))))))
      | ~ v1_funct_2(D_8508,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_8510),u1_pre_topc(B_8510))))
      | ~ m1_subset_1(D_8508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_8510))))
      | ~ v1_funct_2(D_8508,u1_struct_0('#skF_1'),u1_struct_0(B_8510))
      | ~ v1_funct_1(D_8508)
      | ~ l1_pre_topc(B_8510)
      | ~ v2_pre_topc(B_8510)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57519,c_58249])).

tff(c_60431,plain,(
    ! [D_8683,B_8684] :
      ( v5_pre_topc(D_8683,'#skF_1',g1_pre_topc(u1_struct_0(B_8684),u1_pre_topc(B_8684)))
      | ~ v5_pre_topc(D_8683,'#skF_1',B_8684)
      | ~ m1_subset_1(D_8683,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_8684),u1_pre_topc(B_8684))))))
      | ~ v1_funct_2(D_8683,k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_8684),u1_pre_topc(B_8684))))
      | ~ m1_subset_1(D_8683,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_8684))))
      | ~ v1_funct_2(D_8683,k1_relat_1('#skF_4'),u1_struct_0(B_8684))
      | ~ v1_funct_1(D_8683)
      | ~ l1_pre_topc(B_8684)
      | ~ v2_pre_topc(B_8684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_57519,c_57519,c_57519,c_58258])).

tff(c_60437,plain,
    ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58192,c_60431])).

tff(c_60456,plain,(
    v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_57527,c_57526,c_58193,c_56927,c_60437])).

tff(c_60458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60132,c_60456])).

tff(c_60459,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60130])).

tff(c_60463,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56959,c_60459])).

tff(c_60467,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_60463])).

tff(c_60468,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_57084])).

tff(c_60480,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60468,c_144])).

tff(c_60500,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60480,c_60480,c_8])).

tff(c_60469,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_57084])).

tff(c_60481,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_60468,c_4])).

tff(c_60690,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60469,c_60481])).

tff(c_57060,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_60814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60468,c_60500,c_60690,c_57060])).

tff(c_60815,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_57085])).

tff(c_60827,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60815,c_144])).

tff(c_60846,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60827,c_60827,c_8])).

tff(c_60816,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_57085])).

tff(c_60901,plain,(
    ! [A_8720] :
      ( A_8720 = '#skF_4'
      | ~ v1_xboole_0(A_8720) ) ),
    inference(resolution,[status(thm)],[c_60815,c_4])).

tff(c_60908,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60816,c_60901])).

tff(c_56976,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_60914,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60908,c_56976])).

tff(c_61138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60815,c_60846,c_60914])).

tff(c_61139,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_61151,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61139,c_144])).

tff(c_61169,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61151,c_61151,c_10])).

tff(c_61168,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61151,c_20])).

tff(c_61469,plain,(
    ! [A_8779,B_8780,C_8781] :
      ( k1_relset_1(A_8779,B_8780,C_8781) = k1_relat_1(C_8781)
      | ~ m1_subset_1(C_8781,k1_zfmisc_1(k2_zfmisc_1(A_8779,B_8780))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_61484,plain,(
    ! [A_8779,B_8780] : k1_relset_1(A_8779,B_8780,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_61168,c_61469])).

tff(c_61776,plain,(
    ! [C_8820,A_8821,B_8822] :
      ( v1_funct_2(C_8820,A_8821,B_8822)
      | k1_relset_1(A_8821,B_8822,C_8820) != A_8821
      | ~ m1_subset_1(C_8820,k1_zfmisc_1(k2_zfmisc_1(A_8821,B_8822)))
      | ~ v1_funct_1(C_8820) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_61780,plain,(
    ! [A_8821,B_8822] :
      ( v1_funct_2('#skF_4',A_8821,B_8822)
      | k1_relset_1(A_8821,B_8822,'#skF_4') != A_8821
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_61168,c_61776])).

tff(c_61793,plain,(
    ! [A_8821,B_8822] :
      ( v1_funct_2('#skF_4',A_8821,B_8822)
      | k1_relat_1('#skF_4') != A_8821 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61484,c_61780])).

tff(c_62103,plain,(
    ! [C_8835,A_8836,B_8837] :
      ( ~ v1_xboole_0(C_8835)
      | ~ v1_funct_2(C_8835,A_8836,B_8837)
      | ~ v1_funct_1(C_8835)
      | ~ m1_subset_1(C_8835,k1_zfmisc_1(k2_zfmisc_1(A_8836,B_8837)))
      | v1_xboole_0(B_8837)
      | v1_xboole_0(A_8836) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_62107,plain,(
    ! [A_8836,B_8837] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_8836,B_8837)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_8837)
      | v1_xboole_0(A_8836) ) ),
    inference(resolution,[status(thm)],[c_61168,c_62103])).

tff(c_62323,plain,(
    ! [A_8843,B_8844] :
      ( ~ v1_funct_2('#skF_4',A_8843,B_8844)
      | v1_xboole_0(B_8844)
      | v1_xboole_0(A_8843) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61139,c_62107])).

tff(c_62327,plain,(
    ! [B_8822,A_8821] :
      ( v1_xboole_0(B_8822)
      | v1_xboole_0(A_8821)
      | k1_relat_1('#skF_4') != A_8821 ) ),
    inference(resolution,[status(thm)],[c_61793,c_62323])).

tff(c_62371,plain,(
    ! [A_8848] :
      ( v1_xboole_0(A_8848)
      | k1_relat_1('#skF_4') != A_8848 ) ),
    inference(splitLeft,[status(thm)],[c_62327])).

tff(c_61152,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_61139,c_4])).

tff(c_62429,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62371,c_61152])).

tff(c_61163,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61151,c_61151,c_40388])).

tff(c_61811,plain,(
    ! [A_8823,B_8824] :
      ( v1_funct_2('#skF_4',A_8823,B_8824)
      | k1_relat_1('#skF_4') != A_8823 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61484,c_61780])).

tff(c_61164,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61151,c_61151,c_40375])).

tff(c_61568,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,'#skF_4')
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61164,c_61151,c_61151,c_61151,c_113])).

tff(c_61818,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_61811,c_61568])).

tff(c_61822,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61163,c_61818])).

tff(c_61846,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_61822])).

tff(c_62447,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62429,c_61846])).

tff(c_62448,plain,(
    ! [B_8822] : v1_xboole_0(B_8822) ),
    inference(splitRight,[status(thm)],[c_62327])).

tff(c_61170,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61151,c_61151,c_8])).

tff(c_61647,plain,(
    ! [C_8815,A_8816,B_8817] :
      ( v1_partfun1(C_8815,A_8816)
      | ~ v1_funct_2(C_8815,A_8816,B_8817)
      | ~ v1_funct_1(C_8815)
      | ~ m1_subset_1(C_8815,k1_zfmisc_1(k2_zfmisc_1(A_8816,B_8817)))
      | v1_xboole_0(B_8817) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_61651,plain,(
    ! [A_8816,B_8817] :
      ( v1_partfun1('#skF_4',A_8816)
      | ~ v1_funct_2('#skF_4',A_8816,B_8817)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_8817) ) ),
    inference(resolution,[status(thm)],[c_61168,c_61647])).

tff(c_61668,plain,(
    ! [A_8818,B_8819] :
      ( v1_partfun1('#skF_4',A_8818)
      | ~ v1_funct_2('#skF_4',A_8818,B_8819)
      | v1_xboole_0(B_8819) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61651])).

tff(c_61675,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_107,c_61668])).

tff(c_61677,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_61675])).

tff(c_61692,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61677,c_61152])).

tff(c_61700,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61692,c_56976])).

tff(c_61707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61139,c_61170,c_61700])).

tff(c_61708,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_61675])).

tff(c_61223,plain,(
    ! [A_8735] : k2_zfmisc_1(A_8735,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61151,c_61151,c_8])).

tff(c_30,plain,(
    ! [C_19,A_17,B_18] :
      ( v4_relat_1(C_19,A_17)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_61228,plain,(
    ! [C_19,A_8735] :
      ( v4_relat_1(C_19,A_8735)
      | ~ m1_subset_1(C_19,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61223,c_30])).

tff(c_61237,plain,(
    ! [C_19,A_8735] :
      ( v4_relat_1(C_19,A_8735)
      | ~ m1_subset_1(C_19,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61164,c_61228])).

tff(c_61422,plain,(
    ! [B_8765,A_8766] :
      ( k1_relat_1(B_8765) = A_8766
      | ~ v1_partfun1(B_8765,A_8766)
      | ~ v4_relat_1(B_8765,A_8766)
      | ~ v1_relat_1(B_8765) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_61429,plain,(
    ! [C_19,A_8735] :
      ( k1_relat_1(C_19) = A_8735
      | ~ v1_partfun1(C_19,A_8735)
      | ~ v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_61237,c_61422])).

tff(c_61712,plain,
    ( u1_struct_0('#skF_1') = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_61708,c_61429])).

tff(c_61721,plain,(
    u1_struct_0('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61163,c_220,c_61712])).

tff(c_61729,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61721,c_56976])).

tff(c_62511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62448,c_61729])).

tff(c_62513,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_61822])).

tff(c_62534,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4',u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62513,c_61729])).

tff(c_62542,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61139,c_61169,c_62534])).

tff(c_62543,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_62582,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62543,c_144])).

tff(c_62588,plain,(
    m1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_62582,c_40388])).

tff(c_62544,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_62592,plain,(
    ! [A_92] :
      ( A_92 = '#skF_4'
      | ~ v1_xboole_0(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_144])).

tff(c_62779,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62544,c_62592])).

tff(c_62846,plain,(
    ! [B_8883,A_8884] :
      ( B_8883 = '#skF_4'
      | A_8884 = '#skF_4'
      | k2_zfmisc_1(A_8884,B_8883) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_62582,c_62582,c_6])).

tff(c_62856,plain,
    ( u1_struct_0('#skF_2') = '#skF_4'
    | u1_struct_0('#skF_1') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_62779,c_62846])).

tff(c_62861,plain,(
    u1_struct_0('#skF_1') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_62856])).

tff(c_62863,plain,(
    v1_funct_2('#skF_4','#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62861,c_107])).

tff(c_62589,plain,(
    k1_zfmisc_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_62582,c_40375])).

tff(c_63117,plain,(
    ! [C_8925,B_8926] :
      ( v1_partfun1(C_8925,'#skF_4')
      | ~ v1_funct_2(C_8925,'#skF_4',B_8926)
      | ~ m1_subset_1(C_8925,'#skF_4')
      | ~ v1_funct_1(C_8925) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62589,c_62582,c_62582,c_62582,c_113])).

tff(c_63120,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62863,c_63117])).

tff(c_63123,plain,(
    v1_partfun1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62588,c_63120])).

tff(c_62593,plain,(
    ! [A_7] : m1_subset_1('#skF_4',k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_20])).

tff(c_62660,plain,(
    ! [C_8856,A_8857,B_8858] :
      ( v4_relat_1(C_8856,A_8857)
      | ~ m1_subset_1(C_8856,k1_zfmisc_1(k2_zfmisc_1(A_8857,B_8858))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62669,plain,(
    ! [A_8857] : v4_relat_1('#skF_4',A_8857) ),
    inference(resolution,[status(thm)],[c_62593,c_62660])).

tff(c_63019,plain,(
    ! [B_8907,A_8908] :
      ( k1_relat_1(B_8907) = A_8908
      | ~ v1_partfun1(B_8907,A_8908)
      | ~ v4_relat_1(B_8907,A_8908)
      | ~ v1_relat_1(B_8907) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_63028,plain,(
    ! [A_8857] :
      ( k1_relat_1('#skF_4') = A_8857
      | ~ v1_partfun1('#skF_4',A_8857)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62669,c_63019])).

tff(c_63033,plain,(
    ! [A_8857] :
      ( k1_relat_1('#skF_4') = A_8857
      | ~ v1_partfun1('#skF_4',A_8857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_63028])).

tff(c_63127,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_63123,c_63033])).

tff(c_63062,plain,(
    ! [A_8913,B_8914,C_8915] :
      ( k1_relset_1(A_8913,B_8914,C_8915) = k1_relat_1(C_8915)
      | ~ m1_subset_1(C_8915,k1_zfmisc_1(k2_zfmisc_1(A_8913,B_8914))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63079,plain,(
    ! [A_8913,B_8914] : k1_relset_1(A_8913,B_8914,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62593,c_63062])).

tff(c_63128,plain,(
    ! [A_8913,B_8914] : k1_relset_1(A_8913,B_8914,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63127,c_63079])).

tff(c_76301,plain,(
    ! [C_11991,A_11992,B_11993] :
      ( v1_funct_2(C_11991,A_11992,B_11993)
      | k1_relset_1(A_11992,B_11993,C_11991) != A_11992
      | ~ m1_subset_1(C_11991,k1_zfmisc_1(k2_zfmisc_1(A_11992,B_11993)))
      | ~ v1_funct_1(C_11991) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_76311,plain,(
    ! [A_11992,B_11993] :
      ( v1_funct_2('#skF_4',A_11992,B_11993)
      | k1_relset_1(A_11992,B_11993,'#skF_4') != A_11992
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62593,c_76301])).

tff(c_76367,plain,(
    ! [B_11993] : v1_funct_2('#skF_4','#skF_4',B_11993) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63128,c_76311])).

tff(c_76320,plain,(
    ! [A_11992,B_11993] :
      ( v1_funct_2('#skF_4',A_11992,B_11993)
      | A_11992 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63128,c_76311])).

tff(c_62594,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_4',B_4) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_62582,c_10])).

tff(c_76636,plain,(
    ! [D_12018,A_12019,B_12020] :
      ( v5_pre_topc(D_12018,A_12019,g1_pre_topc(u1_struct_0(B_12020),u1_pre_topc(B_12020)))
      | ~ v5_pre_topc(D_12018,A_12019,B_12020)
      | ~ m1_subset_1(D_12018,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12019),u1_struct_0(g1_pre_topc(u1_struct_0(B_12020),u1_pre_topc(B_12020))))))
      | ~ v1_funct_2(D_12018,u1_struct_0(A_12019),u1_struct_0(g1_pre_topc(u1_struct_0(B_12020),u1_pre_topc(B_12020))))
      | ~ m1_subset_1(D_12018,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12019),u1_struct_0(B_12020))))
      | ~ v1_funct_2(D_12018,u1_struct_0(A_12019),u1_struct_0(B_12020))
      | ~ v1_funct_1(D_12018)
      | ~ l1_pre_topc(B_12020)
      | ~ v2_pre_topc(B_12020)
      | ~ l1_pre_topc(A_12019)
      | ~ v2_pre_topc(A_12019) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_76651,plain,(
    ! [D_12018,B_12020] :
      ( v5_pre_topc(D_12018,'#skF_1',g1_pre_topc(u1_struct_0(B_12020),u1_pre_topc(B_12020)))
      | ~ v5_pre_topc(D_12018,'#skF_1',B_12020)
      | ~ m1_subset_1(D_12018,k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_12020),u1_pre_topc(B_12020))))))
      | ~ v1_funct_2(D_12018,u1_struct_0('#skF_1'),u1_struct_0(g1_pre_topc(u1_struct_0(B_12020),u1_pre_topc(B_12020))))
      | ~ m1_subset_1(D_12018,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_12020))))
      | ~ v1_funct_2(D_12018,u1_struct_0('#skF_1'),u1_struct_0(B_12020))
      | ~ v1_funct_1(D_12018)
      | ~ l1_pre_topc(B_12020)
      | ~ v2_pre_topc(B_12020)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62861,c_76636])).

tff(c_77695,plain,(
    ! [D_12135,B_12136] :
      ( v5_pre_topc(D_12135,'#skF_1',g1_pre_topc(u1_struct_0(B_12136),u1_pre_topc(B_12136)))
      | ~ v5_pre_topc(D_12135,'#skF_1',B_12136)
      | ~ v1_funct_2(D_12135,'#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_12136),u1_pre_topc(B_12136))))
      | ~ m1_subset_1(D_12135,'#skF_4')
      | ~ v1_funct_2(D_12135,'#skF_4',u1_struct_0(B_12136))
      | ~ v1_funct_1(D_12135)
      | ~ l1_pre_topc(B_12136)
      | ~ v2_pre_topc(B_12136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_62861,c_62589,c_62594,c_62861,c_62861,c_62589,c_62594,c_76651])).

tff(c_77707,plain,(
    ! [B_12136] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_12136),u1_pre_topc(B_12136)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_12136)
      | ~ m1_subset_1('#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_12136))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_12136)
      | ~ v2_pre_topc(B_12136) ) ),
    inference(resolution,[status(thm)],[c_76320,c_77695])).

tff(c_77733,plain,(
    ! [B_12137] :
      ( v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0(B_12137),u1_pre_topc(B_12137)))
      | ~ v5_pre_topc('#skF_4','#skF_1',B_12137)
      | ~ l1_pre_topc(B_12137)
      | ~ v2_pre_topc(B_12137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_76367,c_62588,c_77707])).

tff(c_63355,plain,(
    ! [C_8950,A_8951,B_8952] :
      ( v1_funct_2(C_8950,A_8951,B_8952)
      | k1_relset_1(A_8951,B_8952,C_8950) != A_8951
      | ~ m1_subset_1(C_8950,k1_zfmisc_1(k2_zfmisc_1(A_8951,B_8952)))
      | ~ v1_funct_1(C_8950) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63365,plain,(
    ! [A_8951,B_8952] :
      ( v1_funct_2('#skF_4',A_8951,B_8952)
      | k1_relset_1(A_8951,B_8952,'#skF_4') != A_8951
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62593,c_63355])).

tff(c_63376,plain,(
    ! [B_8952] : v1_funct_2('#skF_4','#skF_4',B_8952) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63128,c_63365])).

tff(c_63374,plain,(
    ! [A_8951,B_8952] :
      ( v1_funct_2('#skF_4',A_8951,B_8952)
      | A_8951 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63128,c_63365])).

tff(c_63453,plain,(
    ! [C_8963,A_8964,B_8965] :
      ( ~ v1_xboole_0(C_8963)
      | ~ v1_funct_2(C_8963,A_8964,B_8965)
      | ~ v1_funct_1(C_8963)
      | ~ m1_subset_1(C_8963,k1_zfmisc_1(k2_zfmisc_1(A_8964,B_8965)))
      | v1_xboole_0(B_8965)
      | v1_xboole_0(A_8964) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_63463,plain,(
    ! [A_8964,B_8965] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_8964,B_8965)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_8965)
      | v1_xboole_0(A_8964) ) ),
    inference(resolution,[status(thm)],[c_62593,c_63453])).

tff(c_63474,plain,(
    ! [A_8966,B_8967] :
      ( ~ v1_funct_2('#skF_4',A_8966,B_8967)
      | v1_xboole_0(B_8967)
      | v1_xboole_0(A_8966) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62543,c_63463])).

tff(c_63481,plain,(
    ! [B_8952,A_8951] :
      ( v1_xboole_0(B_8952)
      | v1_xboole_0(A_8951)
      | A_8951 != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_63374,c_63474])).

tff(c_63485,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_63481])).

tff(c_62595,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_62582,c_8])).

tff(c_62875,plain,
    ( m1_subset_1(u1_pre_topc('#skF_1'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_62861,c_64])).

tff(c_62883,plain,(
    m1_subset_1(u1_pre_topc('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_62589,c_62589,c_62875])).

tff(c_62585,plain,(
    ! [B_10] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_40393])).

tff(c_62900,plain,(
    v1_xboole_0(u1_pre_topc('#skF_1')) ),
    inference(resolution,[status(thm)],[c_62883,c_62585])).

tff(c_62913,plain,(
    u1_pre_topc('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62900,c_62592])).

tff(c_62864,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62861,c_82])).

tff(c_62918,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62913,c_62864])).

tff(c_63158,plain,(
    ! [C_8929,A_8930,B_8931] :
      ( v1_partfun1(C_8929,A_8930)
      | ~ v1_funct_2(C_8929,A_8930,B_8931)
      | ~ v1_funct_1(C_8929)
      | ~ m1_subset_1(C_8929,k1_zfmisc_1(k2_zfmisc_1(A_8930,B_8931)))
      | v1_xboole_0(B_8931) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_63168,plain,(
    ! [A_8930,B_8931] :
      ( v1_partfun1('#skF_4',A_8930)
      | ~ v1_funct_2('#skF_4',A_8930,B_8931)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_8931) ) ),
    inference(resolution,[status(thm)],[c_62593,c_63158])).

tff(c_63204,plain,(
    ! [A_8935,B_8936] :
      ( v1_partfun1('#skF_4',A_8935)
      | ~ v1_funct_2('#skF_4',A_8935,B_8936)
      | v1_xboole_0(B_8936) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_63168])).

tff(c_63211,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_62918,c_63204])).

tff(c_63291,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_63211])).

tff(c_63306,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_63291,c_62592])).

tff(c_63593,plain,(
    ! [D_8978,A_8979,B_8980] :
      ( v5_pre_topc(D_8978,A_8979,g1_pre_topc(u1_struct_0(B_8980),u1_pre_topc(B_8980)))
      | ~ v5_pre_topc(D_8978,A_8979,B_8980)
      | ~ m1_subset_1(D_8978,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8979),u1_struct_0(g1_pre_topc(u1_struct_0(B_8980),u1_pre_topc(B_8980))))))
      | ~ v1_funct_2(D_8978,u1_struct_0(A_8979),u1_struct_0(g1_pre_topc(u1_struct_0(B_8980),u1_pre_topc(B_8980))))
      | ~ m1_subset_1(D_8978,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8979),u1_struct_0(B_8980))))
      | ~ v1_funct_2(D_8978,u1_struct_0(A_8979),u1_struct_0(B_8980))
      | ~ v1_funct_1(D_8978)
      | ~ l1_pre_topc(B_8980)
      | ~ v2_pre_topc(B_8980)
      | ~ l1_pre_topc(A_8979)
      | ~ v2_pre_topc(A_8979) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_64461,plain,(
    ! [B_9057,A_9058,B_9059] :
      ( v5_pre_topc(B_9057,A_9058,g1_pre_topc(u1_struct_0(B_9059),u1_pre_topc(B_9059)))
      | ~ v5_pre_topc(B_9057,A_9058,B_9059)
      | ~ v1_funct_2(B_9057,u1_struct_0(A_9058),u1_struct_0(g1_pre_topc(u1_struct_0(B_9059),u1_pre_topc(B_9059))))
      | ~ m1_subset_1(B_9057,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058),u1_struct_0(B_9059))))
      | ~ v1_funct_2(B_9057,u1_struct_0(A_9058),u1_struct_0(B_9059))
      | ~ v1_funct_1(B_9057)
      | ~ l1_pre_topc(B_9059)
      | ~ v2_pre_topc(B_9059)
      | ~ l1_pre_topc(A_9058)
      | ~ v2_pre_topc(A_9058)
      | ~ v1_xboole_0(B_9057)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058),u1_struct_0(g1_pre_topc(u1_struct_0(B_9059),u1_pre_topc(B_9059)))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_63593])).

tff(c_64472,plain,(
    ! [B_9057,A_9058] :
      ( v5_pre_topc(B_9057,A_9058,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(B_9057,A_9058,'#skF_2')
      | ~ v1_funct_2(B_9057,u1_struct_0(A_9058),'#skF_4')
      | ~ m1_subset_1(B_9057,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(B_9057,u1_struct_0(A_9058),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_9057)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_9058)
      | ~ v2_pre_topc(A_9058)
      | ~ v1_xboole_0(B_9057)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63306,c_64461])).

tff(c_64541,plain,(
    ! [B_9068,A_9069] :
      ( v5_pre_topc(B_9068,A_9069,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(B_9068,A_9069,'#skF_2')
      | ~ v1_funct_2(B_9068,u1_struct_0(A_9069),'#skF_4')
      | ~ m1_subset_1(B_9068,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9069),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(B_9068,u1_struct_0(A_9069),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_9068)
      | ~ l1_pre_topc(A_9069)
      | ~ v2_pre_topc(A_9069)
      | ~ v1_xboole_0(B_9068) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63485,c_62589,c_62595,c_63306,c_94,c_92,c_64472])).

tff(c_64551,plain,(
    ! [A_9069] :
      ( v5_pre_topc('#skF_4',A_9069,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_9069,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9069),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9069),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_9069)
      | ~ v2_pre_topc(A_9069)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62593,c_64541])).

tff(c_64562,plain,(
    ! [A_9069] :
      ( v5_pre_topc('#skF_4',A_9069,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4',A_9069,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9069),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9069),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_9069)
      | ~ v2_pre_topc(A_9069) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63485,c_84,c_64551])).

tff(c_62973,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62913,c_62861,c_56926])).

tff(c_63327,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_63306,c_56959])).

tff(c_63762,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_63327])).

tff(c_63768,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56959,c_63762])).

tff(c_63773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_63768])).

tff(c_63775,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_63327])).

tff(c_63947,plain,(
    ! [D_9013,A_9014,B_9015] :
      ( v5_pre_topc(D_9013,g1_pre_topc(u1_struct_0(A_9014),u1_pre_topc(A_9014)),B_9015)
      | ~ v5_pre_topc(D_9013,A_9014,B_9015)
      | ~ m1_subset_1(D_9013,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_9014),u1_pre_topc(A_9014))),u1_struct_0(B_9015))))
      | ~ v1_funct_2(D_9013,u1_struct_0(g1_pre_topc(u1_struct_0(A_9014),u1_pre_topc(A_9014))),u1_struct_0(B_9015))
      | ~ m1_subset_1(D_9013,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9014),u1_struct_0(B_9015))))
      | ~ v1_funct_2(D_9013,u1_struct_0(A_9014),u1_struct_0(B_9015))
      | ~ v1_funct_1(D_9013)
      | ~ l1_pre_topc(B_9015)
      | ~ v2_pre_topc(B_9015)
      | ~ l1_pre_topc(A_9014)
      | ~ v2_pre_topc(A_9014) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_64789,plain,(
    ! [B_9086,A_9087,B_9088] :
      ( v5_pre_topc(B_9086,g1_pre_topc(u1_struct_0(A_9087),u1_pre_topc(A_9087)),B_9088)
      | ~ v5_pre_topc(B_9086,A_9087,B_9088)
      | ~ v1_funct_2(B_9086,u1_struct_0(g1_pre_topc(u1_struct_0(A_9087),u1_pre_topc(A_9087))),u1_struct_0(B_9088))
      | ~ m1_subset_1(B_9086,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9087),u1_struct_0(B_9088))))
      | ~ v1_funct_2(B_9086,u1_struct_0(A_9087),u1_struct_0(B_9088))
      | ~ v1_funct_1(B_9086)
      | ~ l1_pre_topc(B_9088)
      | ~ v2_pre_topc(B_9088)
      | ~ l1_pre_topc(A_9087)
      | ~ v2_pre_topc(A_9087)
      | ~ v1_xboole_0(B_9086)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_9087),u1_pre_topc(A_9087))),u1_struct_0(B_9088)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_63947])).

tff(c_64798,plain,(
    ! [B_9086,B_9088] :
      ( v5_pre_topc(B_9086,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_9088)
      | ~ v5_pre_topc(B_9086,'#skF_2',B_9088)
      | ~ v1_funct_2(B_9086,'#skF_4',u1_struct_0(B_9088))
      | ~ m1_subset_1(B_9086,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_9088))))
      | ~ v1_funct_2(B_9086,u1_struct_0('#skF_2'),u1_struct_0(B_9088))
      | ~ v1_funct_1(B_9086)
      | ~ l1_pre_topc(B_9088)
      | ~ v2_pre_topc(B_9088)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ v1_xboole_0(B_9086)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_9088)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63306,c_64789])).

tff(c_64847,plain,(
    ! [B_9094,B_9095] :
      ( v5_pre_topc(B_9094,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_9095)
      | ~ v5_pre_topc(B_9094,'#skF_2',B_9095)
      | ~ v1_funct_2(B_9094,'#skF_4',u1_struct_0(B_9095))
      | ~ m1_subset_1(B_9094,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_9095))))
      | ~ v1_funct_2(B_9094,u1_struct_0('#skF_2'),u1_struct_0(B_9095))
      | ~ v1_funct_1(B_9094)
      | ~ l1_pre_topc(B_9095)
      | ~ v2_pre_topc(B_9095)
      | ~ v1_xboole_0(B_9094) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63485,c_62589,c_62594,c_63306,c_94,c_92,c_64798])).

tff(c_64857,plain,(
    ! [B_9095] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_9095)
      | ~ v5_pre_topc('#skF_4','#skF_2',B_9095)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_9095))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_9095))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_9095)
      | ~ v2_pre_topc(B_9095)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62593,c_64847])).

tff(c_64870,plain,(
    ! [B_9096] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_9096)
      | ~ v5_pre_topc('#skF_4','#skF_2',B_9096)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_9096))
      | ~ l1_pre_topc(B_9096)
      | ~ v2_pre_topc(B_9096) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63485,c_84,c_63376,c_64857])).

tff(c_63794,plain,(
    ! [D_9007,A_9008,B_9009] :
      ( v5_pre_topc(D_9007,A_9008,B_9009)
      | ~ v5_pre_topc(D_9007,A_9008,g1_pre_topc(u1_struct_0(B_9009),u1_pre_topc(B_9009)))
      | ~ m1_subset_1(D_9007,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9008),u1_struct_0(g1_pre_topc(u1_struct_0(B_9009),u1_pre_topc(B_9009))))))
      | ~ v1_funct_2(D_9007,u1_struct_0(A_9008),u1_struct_0(g1_pre_topc(u1_struct_0(B_9009),u1_pre_topc(B_9009))))
      | ~ m1_subset_1(D_9007,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9008),u1_struct_0(B_9009))))
      | ~ v1_funct_2(D_9007,u1_struct_0(A_9008),u1_struct_0(B_9009))
      | ~ v1_funct_1(D_9007)
      | ~ l1_pre_topc(B_9009)
      | ~ v2_pre_topc(B_9009)
      | ~ l1_pre_topc(A_9008)
      | ~ v2_pre_topc(A_9008) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_64685,plain,(
    ! [B_9077,A_9078,B_9079] :
      ( v5_pre_topc(B_9077,A_9078,B_9079)
      | ~ v5_pre_topc(B_9077,A_9078,g1_pre_topc(u1_struct_0(B_9079),u1_pre_topc(B_9079)))
      | ~ v1_funct_2(B_9077,u1_struct_0(A_9078),u1_struct_0(g1_pre_topc(u1_struct_0(B_9079),u1_pre_topc(B_9079))))
      | ~ m1_subset_1(B_9077,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078),u1_struct_0(B_9079))))
      | ~ v1_funct_2(B_9077,u1_struct_0(A_9078),u1_struct_0(B_9079))
      | ~ v1_funct_1(B_9077)
      | ~ l1_pre_topc(B_9079)
      | ~ v2_pre_topc(B_9079)
      | ~ l1_pre_topc(A_9078)
      | ~ v2_pre_topc(A_9078)
      | ~ v1_xboole_0(B_9077)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078),u1_struct_0(g1_pre_topc(u1_struct_0(B_9079),u1_pre_topc(B_9079)))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_63794])).

tff(c_64696,plain,(
    ! [B_9077,A_9078] :
      ( v5_pre_topc(B_9077,A_9078,'#skF_2')
      | ~ v5_pre_topc(B_9077,A_9078,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(B_9077,u1_struct_0(A_9078),'#skF_4')
      | ~ m1_subset_1(B_9077,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(B_9077,u1_struct_0(A_9078),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_9077)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_9078)
      | ~ v2_pre_topc(A_9078)
      | ~ v1_xboole_0(B_9077)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63306,c_64685])).

tff(c_64740,plain,(
    ! [B_9081,A_9082] :
      ( v5_pre_topc(B_9081,A_9082,'#skF_2')
      | ~ v5_pre_topc(B_9081,A_9082,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2(B_9081,u1_struct_0(A_9082),'#skF_4')
      | ~ m1_subset_1(B_9081,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9082),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(B_9081,u1_struct_0(A_9082),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(B_9081)
      | ~ l1_pre_topc(A_9082)
      | ~ v2_pre_topc(A_9082)
      | ~ v1_xboole_0(B_9081) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63485,c_62589,c_62595,c_63306,c_94,c_92,c_64696])).

tff(c_64750,plain,(
    ! [A_9082] :
      ( v5_pre_topc('#skF_4',A_9082,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_9082,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9082),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9082),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_9082)
      | ~ v2_pre_topc(A_9082)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62593,c_64740])).

tff(c_64761,plain,(
    ! [A_9082] :
      ( v5_pre_topc('#skF_4',A_9082,'#skF_2')
      | ~ v5_pre_topc('#skF_4',A_9082,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9082),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9082),u1_struct_0('#skF_2'))
      | ~ l1_pre_topc(A_9082)
      | ~ v2_pre_topc(A_9082) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63485,c_84,c_64750])).

tff(c_64874,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64870,c_64761])).

tff(c_64884,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_2')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63775,c_63306,c_63376,c_63306,c_63376,c_63306,c_64874])).

tff(c_64947,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_64884])).

tff(c_64950,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_64947])).

tff(c_64954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_64950])).

tff(c_64956,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64884])).

tff(c_63310,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63306,c_62918])).

tff(c_63972,plain,(
    ! [A_9014,B_9015] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_9014),u1_pre_topc(A_9014)),B_9015)
      | ~ v5_pre_topc('#skF_4',A_9014,B_9015)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_9014),u1_pre_topc(A_9014))),u1_struct_0(B_9015))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9014),u1_struct_0(B_9015))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9014),u1_struct_0(B_9015))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_9015)
      | ~ v2_pre_topc(B_9015)
      | ~ l1_pre_topc(A_9014)
      | ~ v2_pre_topc(A_9014) ) ),
    inference(resolution,[status(thm)],[c_62593,c_63947])).

tff(c_64992,plain,(
    ! [A_9103,B_9104] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_9103),u1_pre_topc(A_9103)),B_9104)
      | ~ v5_pre_topc('#skF_4',A_9103,B_9104)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_9103),u1_pre_topc(A_9103))),u1_struct_0(B_9104))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_9103),u1_struct_0(B_9104))
      | ~ l1_pre_topc(B_9104)
      | ~ v2_pre_topc(B_9104)
      | ~ l1_pre_topc(A_9103)
      | ~ v2_pre_topc(A_9103) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62593,c_63972])).

tff(c_65013,plain,(
    ! [B_9104] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_9104)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_9104)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_9104))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_9104))
      | ~ l1_pre_topc(B_9104)
      | ~ v2_pre_topc(B_9104)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62861,c_64992])).

tff(c_65032,plain,(
    ! [B_9105] :
      ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),B_9105)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_9105)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),u1_struct_0(B_9105))
      | ~ l1_pre_topc(B_9105)
      | ~ v2_pre_topc(B_9105) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_63376,c_62861,c_62913,c_62861,c_62913,c_65013])).

tff(c_65038,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_63306,c_65032])).

tff(c_65044,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64956,c_63775,c_63310,c_65038])).

tff(c_65045,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62973,c_65044])).

tff(c_65050,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64562,c_65045])).

tff(c_65054,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_63376,c_62861,c_63376,c_62861,c_56927,c_65050])).

tff(c_65055,plain,(
    ! [B_8952] : v1_xboole_0(B_8952) ),
    inference(splitRight,[status(thm)],[c_63481])).

tff(c_65109,plain,(
    ! [B_2,A_1] : B_2 = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65055,c_65055,c_4])).

tff(c_65112,plain,(
    ! [B_9107,A_9108] : B_9107 = A_9108 ),
    inference(demodulation,[status(thm),theory(equality)],[c_65055,c_65055,c_4])).

tff(c_76188,plain,(
    ! [A_11968] : ~ v5_pre_topc('#skF_4',g1_pre_topc('#skF_4','#skF_4'),A_11968) ),
    inference(superposition,[status(thm),theory(equality)],[c_65112,c_62973])).

tff(c_76200,plain,(
    ! [B_2,A_11968] : ~ v5_pre_topc('#skF_4',B_2,A_11968) ),
    inference(superposition,[status(thm),theory(equality)],[c_65109,c_76188])).

tff(c_69129,plain,(
    ! [A_1] : A_1 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65055,c_65055,c_4])).

tff(c_68073,plain,(
    ! [B_9107] : B_9107 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65055,c_65055,c_4])).

tff(c_68075,plain,(
    v5_pre_topc('#skF_4','#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_68073,c_56927])).

tff(c_69131,plain,(
    v5_pre_topc('#skF_4','#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69129,c_68075])).

tff(c_76228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76200,c_69131])).

tff(c_76229,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_63211])).

tff(c_63003,plain,(
    ! [B_8901,A_8902,B_8903] :
      ( v4_relat_1(B_8901,A_8902)
      | ~ v1_xboole_0(B_8901)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(A_8902,B_8903))) ) ),
    inference(resolution,[status(thm)],[c_16,c_62660])).

tff(c_63007,plain,(
    ! [B_8901,A_3] :
      ( v4_relat_1(B_8901,A_3)
      | ~ v1_xboole_0(B_8901)
      | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62595,c_63003])).

tff(c_63011,plain,(
    ! [B_8901,A_3] :
      ( v4_relat_1(B_8901,A_3)
      | ~ v1_xboole_0(B_8901) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62543,c_62589,c_63007])).

tff(c_63029,plain,(
    ! [B_8901,A_3] :
      ( k1_relat_1(B_8901) = A_3
      | ~ v1_partfun1(B_8901,A_3)
      | ~ v1_relat_1(B_8901)
      | ~ v1_xboole_0(B_8901) ) ),
    inference(resolution,[status(thm)],[c_63011,c_63019])).

tff(c_76233,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_76229,c_63029])).

tff(c_76239,plain,(
    u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62543,c_220,c_63127,c_76233])).

tff(c_76734,plain,(
    ! [D_12033,A_12034,B_12035] :
      ( v5_pre_topc(D_12033,g1_pre_topc(u1_struct_0(A_12034),u1_pre_topc(A_12034)),B_12035)
      | ~ v5_pre_topc(D_12033,A_12034,B_12035)
      | ~ m1_subset_1(D_12033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12034),u1_pre_topc(A_12034))),u1_struct_0(B_12035))))
      | ~ v1_funct_2(D_12033,u1_struct_0(g1_pre_topc(u1_struct_0(A_12034),u1_pre_topc(A_12034))),u1_struct_0(B_12035))
      | ~ m1_subset_1(D_12033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12034),u1_struct_0(B_12035))))
      | ~ v1_funct_2(D_12033,u1_struct_0(A_12034),u1_struct_0(B_12035))
      | ~ v1_funct_1(D_12033)
      | ~ l1_pre_topc(B_12035)
      | ~ v2_pre_topc(B_12035)
      | ~ l1_pre_topc(A_12034)
      | ~ v2_pre_topc(A_12034) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_76749,plain,(
    ! [D_12033,B_12035] :
      ( v5_pre_topc(D_12033,g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_12035)
      | ~ v5_pre_topc(D_12033,'#skF_1',B_12035)
      | ~ m1_subset_1(D_12033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_1'))),u1_struct_0(B_12035))))
      | ~ v1_funct_2(D_12033,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_12035))
      | ~ m1_subset_1(D_12033,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_12035))))
      | ~ v1_funct_2(D_12033,u1_struct_0('#skF_1'),u1_struct_0(B_12035))
      | ~ v1_funct_1(D_12033)
      | ~ l1_pre_topc(B_12035)
      | ~ v2_pre_topc(B_12035)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62861,c_76734])).

tff(c_76802,plain,(
    ! [D_12042,B_12043] :
      ( v5_pre_topc(D_12042,g1_pre_topc('#skF_4','#skF_4'),B_12043)
      | ~ v5_pre_topc(D_12042,'#skF_1',B_12043)
      | ~ m1_subset_1(D_12042,'#skF_4')
      | ~ v1_funct_2(D_12042,'#skF_4',u1_struct_0(B_12043))
      | ~ v1_funct_1(D_12042)
      | ~ l1_pre_topc(B_12043)
      | ~ v2_pre_topc(B_12043) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_62861,c_62589,c_62594,c_62861,c_76239,c_62861,c_62913,c_62589,c_62594,c_76239,c_62913,c_62861,c_62913,c_76749])).

tff(c_76805,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_76802,c_62973])).

tff(c_76808,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_76367,c_62588,c_76805])).

tff(c_76921,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_76808])).

tff(c_76924,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_76921])).

tff(c_76928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_76924])).

tff(c_76929,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_76808])).

tff(c_77070,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_76929])).

tff(c_77736,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_77733,c_77070])).

tff(c_77752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_56927,c_77736])).

tff(c_77753,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_76929])).

tff(c_77760,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56959,c_77753])).

tff(c_77765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_77760])).

tff(c_77766,plain,(
    u1_struct_0('#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62856])).

tff(c_77769,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77766,c_107])).

tff(c_77946,plain,(
    ! [A_12161,B_12162,C_12163] :
      ( k1_relset_1(A_12161,B_12162,C_12163) = k1_relat_1(C_12163)
      | ~ m1_subset_1(C_12163,k1_zfmisc_1(k2_zfmisc_1(A_12161,B_12162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_77963,plain,(
    ! [A_12161,B_12162] : k1_relset_1(A_12161,B_12162,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62593,c_77946])).

tff(c_80357,plain,(
    ! [C_12955,A_12956,B_12957] :
      ( v1_funct_2(C_12955,A_12956,B_12957)
      | k1_relset_1(A_12956,B_12957,C_12955) != A_12956
      | ~ m1_subset_1(C_12955,k1_zfmisc_1(k2_zfmisc_1(A_12956,B_12957)))
      | ~ v1_funct_1(C_12955) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_80367,plain,(
    ! [A_12956,B_12957] :
      ( v1_funct_2('#skF_4',A_12956,B_12957)
      | k1_relset_1(A_12956,B_12957,'#skF_4') != A_12956
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62593,c_80357])).

tff(c_80376,plain,(
    ! [A_12956,B_12957] :
      ( v1_funct_2('#skF_4',A_12956,B_12957)
      | k1_relat_1('#skF_4') != A_12956 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_77963,c_80367])).

tff(c_80439,plain,(
    ! [C_12965,A_12966,B_12967] :
      ( ~ v1_xboole_0(C_12965)
      | ~ v1_funct_2(C_12965,A_12966,B_12967)
      | ~ v1_funct_1(C_12965)
      | ~ m1_subset_1(C_12965,k1_zfmisc_1(k2_zfmisc_1(A_12966,B_12967)))
      | v1_xboole_0(B_12967)
      | v1_xboole_0(A_12966) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_80449,plain,(
    ! [A_12966,B_12967] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ v1_funct_2('#skF_4',A_12966,B_12967)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_12967)
      | v1_xboole_0(A_12966) ) ),
    inference(resolution,[status(thm)],[c_62593,c_80439])).

tff(c_80460,plain,(
    ! [A_12968,B_12969] :
      ( ~ v1_funct_2('#skF_4',A_12968,B_12969)
      | v1_xboole_0(B_12969)
      | v1_xboole_0(A_12968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62543,c_80449])).

tff(c_80467,plain,(
    ! [B_12957,A_12956] :
      ( v1_xboole_0(B_12957)
      | v1_xboole_0(A_12956)
      | k1_relat_1('#skF_4') != A_12956 ) ),
    inference(resolution,[status(thm)],[c_80376,c_80460])).

tff(c_80472,plain,(
    ! [A_12970] :
      ( v1_xboole_0(A_12970)
      | k1_relat_1('#skF_4') != A_12970 ) ),
    inference(splitLeft,[status(thm)],[c_80467])).

tff(c_80514,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_80472,c_62592])).

tff(c_80380,plain,(
    ! [A_12958,B_12959] :
      ( v1_funct_2('#skF_4',A_12958,B_12959)
      | k1_relat_1('#skF_4') != A_12958 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_77963,c_80367])).

tff(c_78044,plain,(
    ! [C_42,B_41] :
      ( v1_partfun1(C_42,'#skF_4')
      | ~ v1_funct_2(C_42,'#skF_4',B_41)
      | ~ m1_subset_1(C_42,'#skF_4')
      | ~ v1_funct_1(C_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62589,c_62582,c_62582,c_62582,c_113])).

tff(c_80387,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_80380,c_78044])).

tff(c_80394,plain,
    ( v1_partfun1('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62588,c_80387])).

tff(c_80396,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_80394])).

tff(c_80526,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80514,c_80396])).

tff(c_80527,plain,(
    ! [B_12957] : v1_xboole_0(B_12957) ),
    inference(splitRight,[status(thm)],[c_80467])).

tff(c_77781,plain,
    ( m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77766,c_64])).

tff(c_77789,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_62589,c_62589,c_77781])).

tff(c_77800,plain,(
    v1_xboole_0(u1_pre_topc('#skF_2')) ),
    inference(resolution,[status(thm)],[c_77789,c_62585])).

tff(c_77819,plain,(
    u1_pre_topc('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_77800,c_62592])).

tff(c_77770,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77766,c_82])).

tff(c_77823,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77819,c_77770])).

tff(c_77983,plain,(
    ! [C_12168,A_12169,B_12170] :
      ( v1_partfun1(C_12168,A_12169)
      | ~ v1_funct_2(C_12168,A_12169,B_12170)
      | ~ v1_funct_1(C_12168)
      | ~ m1_subset_1(C_12168,k1_zfmisc_1(k2_zfmisc_1(A_12169,B_12170)))
      | v1_xboole_0(B_12170) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_77993,plain,(
    ! [A_12169,B_12170] :
      ( v1_partfun1('#skF_4',A_12169)
      | ~ v1_funct_2('#skF_4',A_12169,B_12170)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(B_12170) ) ),
    inference(resolution,[status(thm)],[c_62593,c_77983])).

tff(c_78009,plain,(
    ! [A_12173,B_12174] :
      ( v1_partfun1('#skF_4',A_12173)
      | ~ v1_funct_2('#skF_4',A_12173,B_12174)
      | v1_xboole_0(B_12174) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_77993])).

tff(c_78016,plain,
    ( v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_77823,c_78009])).

tff(c_78070,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_78016])).

tff(c_78085,plain,(
    u1_struct_0(g1_pre_topc('#skF_4','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_78070,c_62592])).

tff(c_78914,plain,(
    ! [D_12803,A_12804,B_12805] :
      ( v5_pre_topc(D_12803,A_12804,g1_pre_topc(u1_struct_0(B_12805),u1_pre_topc(B_12805)))
      | ~ v5_pre_topc(D_12803,A_12804,B_12805)
      | ~ m1_subset_1(D_12803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804),u1_struct_0(g1_pre_topc(u1_struct_0(B_12805),u1_pre_topc(B_12805))))))
      | ~ v1_funct_2(D_12803,u1_struct_0(A_12804),u1_struct_0(g1_pre_topc(u1_struct_0(B_12805),u1_pre_topc(B_12805))))
      | ~ m1_subset_1(D_12803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804),u1_struct_0(B_12805))))
      | ~ v1_funct_2(D_12803,u1_struct_0(A_12804),u1_struct_0(B_12805))
      | ~ v1_funct_1(D_12803)
      | ~ l1_pre_topc(B_12805)
      | ~ v2_pre_topc(B_12805)
      | ~ l1_pre_topc(A_12804)
      | ~ v2_pre_topc(A_12804) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_78932,plain,(
    ! [D_12803,A_12804] :
      ( v5_pre_topc(D_12803,A_12804,g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc(D_12803,A_12804,'#skF_2')
      | ~ m1_subset_1(D_12803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_2'))))))
      | ~ v1_funct_2(D_12803,u1_struct_0(A_12804),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ m1_subset_1(D_12803,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(D_12803,u1_struct_0(A_12804),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(D_12803)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_12804)
      | ~ v2_pre_topc(A_12804) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77766,c_78914])).

tff(c_80162,plain,(
    ! [D_12937,A_12938] :
      ( v5_pre_topc(D_12937,A_12938,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_12937,A_12938,'#skF_2')
      | ~ m1_subset_1(D_12937,'#skF_4')
      | ~ v1_funct_2(D_12937,u1_struct_0(A_12938),'#skF_4')
      | ~ v1_funct_1(D_12937)
      | ~ l1_pre_topc(A_12938)
      | ~ v2_pre_topc(A_12938) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_77766,c_62589,c_62595,c_77766,c_78085,c_77766,c_77819,c_62589,c_62595,c_78085,c_77819,c_77766,c_77819,c_78932])).

tff(c_78089,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78085,c_77823])).

tff(c_77833,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77819,c_66])).

tff(c_77846,plain,(
    v2_pre_topc(g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_77766,c_77833])).

tff(c_62587,plain,(
    ! [A_3824] : l1_pre_topc(g1_pre_topc(A_3824,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62582,c_40369])).

tff(c_79181,plain,(
    ! [D_12838,A_12839,B_12840] :
      ( v5_pre_topc(D_12838,g1_pre_topc(u1_struct_0(A_12839),u1_pre_topc(A_12839)),B_12840)
      | ~ v5_pre_topc(D_12838,A_12839,B_12840)
      | ~ m1_subset_1(D_12838,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12839),u1_pre_topc(A_12839))),u1_struct_0(B_12840))))
      | ~ v1_funct_2(D_12838,u1_struct_0(g1_pre_topc(u1_struct_0(A_12839),u1_pre_topc(A_12839))),u1_struct_0(B_12840))
      | ~ m1_subset_1(D_12838,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12839),u1_struct_0(B_12840))))
      | ~ v1_funct_2(D_12838,u1_struct_0(A_12839),u1_struct_0(B_12840))
      | ~ v1_funct_1(D_12838)
      | ~ l1_pre_topc(B_12840)
      | ~ v2_pre_topc(B_12840)
      | ~ l1_pre_topc(A_12839)
      | ~ v2_pre_topc(A_12839) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_79190,plain,(
    ! [D_12838,A_12839] :
      ( v5_pre_topc(D_12838,g1_pre_topc(u1_struct_0(A_12839),u1_pre_topc(A_12839)),g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_12838,A_12839,g1_pre_topc('#skF_4','#skF_4'))
      | ~ m1_subset_1(D_12838,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12839),u1_pre_topc(A_12839))),'#skF_4')))
      | ~ v1_funct_2(D_12838,u1_struct_0(g1_pre_topc(u1_struct_0(A_12839),u1_pre_topc(A_12839))),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
      | ~ m1_subset_1(D_12838,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12839),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))))
      | ~ v1_funct_2(D_12838,u1_struct_0(A_12839),u1_struct_0(g1_pre_topc('#skF_4','#skF_4')))
      | ~ v1_funct_1(D_12838)
      | ~ l1_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ v2_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
      | ~ l1_pre_topc(A_12839)
      | ~ v2_pre_topc(A_12839) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78085,c_79181])).

tff(c_79409,plain,(
    ! [D_12867,A_12868] :
      ( v5_pre_topc(D_12867,g1_pre_topc(u1_struct_0(A_12868),u1_pre_topc(A_12868)),g1_pre_topc('#skF_4','#skF_4'))
      | ~ v5_pre_topc(D_12867,A_12868,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v1_funct_2(D_12867,u1_struct_0(g1_pre_topc(u1_struct_0(A_12868),u1_pre_topc(A_12868))),'#skF_4')
      | ~ m1_subset_1(D_12867,'#skF_4')
      | ~ v1_funct_2(D_12867,u1_struct_0(A_12868),'#skF_4')
      | ~ v1_funct_1(D_12867)
      | ~ l1_pre_topc(A_12868)
      | ~ v2_pre_topc(A_12868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77846,c_62587,c_78085,c_62589,c_62595,c_78085,c_78085,c_62589,c_62595,c_79190])).

tff(c_77859,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77819,c_77766,c_56926])).

tff(c_79415,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),'#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_79409,c_77859])).

tff(c_79431,plain,(
    ~ v5_pre_topc('#skF_4','#skF_1',g1_pre_topc('#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_77769,c_62588,c_78089,c_79415])).

tff(c_80184,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80162,c_79431])).

tff(c_80208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84,c_77769,c_62588,c_56927,c_80184])).

tff(c_80210,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_78016])).

tff(c_80584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80527,c_80210])).

tff(c_80586,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_80394])).

tff(c_80712,plain,(
    ! [B_12957] : v1_funct_2('#skF_4','#skF_4',B_12957) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80586,c_80376])).

tff(c_80209,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_78016])).

tff(c_77893,plain,(
    ! [B_12146,A_12147] :
      ( k1_relat_1(B_12146) = A_12147
      | ~ v1_partfun1(B_12146,A_12147)
      | ~ v4_relat_1(B_12146,A_12147)
      | ~ v1_relat_1(B_12146) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_77899,plain,(
    ! [A_8857] :
      ( k1_relat_1('#skF_4') = A_8857
      | ~ v1_partfun1('#skF_4',A_8857)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62669,c_77893])).

tff(c_77903,plain,(
    ! [A_8857] :
      ( k1_relat_1('#skF_4') = A_8857
      | ~ v1_partfun1('#skF_4',A_8857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_77899])).

tff(c_80214,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80209,c_77903])).

tff(c_80599,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80586,c_80214])).

tff(c_80898,plain,(
    ! [D_12987,A_12988,B_12989] :
      ( v5_pre_topc(D_12987,g1_pre_topc(u1_struct_0(A_12988),u1_pre_topc(A_12988)),B_12989)
      | ~ v5_pre_topc(D_12987,A_12988,B_12989)
      | ~ m1_subset_1(D_12987,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12988),u1_pre_topc(A_12988))),u1_struct_0(B_12989))))
      | ~ v1_funct_2(D_12987,u1_struct_0(g1_pre_topc(u1_struct_0(A_12988),u1_pre_topc(A_12988))),u1_struct_0(B_12989))
      | ~ m1_subset_1(D_12987,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988),u1_struct_0(B_12989))))
      | ~ v1_funct_2(D_12987,u1_struct_0(A_12988),u1_struct_0(B_12989))
      | ~ v1_funct_1(D_12987)
      | ~ l1_pre_topc(B_12989)
      | ~ v2_pre_topc(B_12989)
      | ~ l1_pre_topc(A_12988)
      | ~ v2_pre_topc(A_12988) ) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_80923,plain,(
    ! [A_12988,B_12989] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_12988),u1_pre_topc(A_12988)),B_12989)
      | ~ v5_pre_topc('#skF_4',A_12988,B_12989)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_12988),u1_pre_topc(A_12988))),u1_struct_0(B_12989))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988),u1_struct_0(B_12989))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_12988),u1_struct_0(B_12989))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_12989)
      | ~ v2_pre_topc(B_12989)
      | ~ l1_pre_topc(A_12988)
      | ~ v2_pre_topc(A_12988) ) ),
    inference(resolution,[status(thm)],[c_62593,c_80898])).

tff(c_82575,plain,(
    ! [A_13136,B_13137] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_13136),u1_pre_topc(A_13136)),B_13137)
      | ~ v5_pre_topc('#skF_4',A_13136,B_13137)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_13136),u1_pre_topc(A_13136))),u1_struct_0(B_13137))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_13136),u1_struct_0(B_13137))
      | ~ l1_pre_topc(B_13137)
      | ~ v2_pre_topc(B_13137)
      | ~ l1_pre_topc(A_13136)
      | ~ v2_pre_topc(A_13136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62593,c_80923])).

tff(c_82587,plain,(
    ! [B_13137] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_13137)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_13137)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_13137))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_13137))
      | ~ l1_pre_topc(B_13137)
      | ~ v2_pre_topc(B_13137)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80599,c_82575])).

tff(c_82606,plain,(
    ! [B_13137] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_13137)
      | ~ v5_pre_topc('#skF_4','#skF_1',B_13137)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0(B_13137))
      | ~ l1_pre_topc(B_13137)
      | ~ v2_pre_topc(B_13137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_80712,c_82587])).

tff(c_62737,plain,(
    ! [A_8864,B_8865] :
      ( v1_pre_topc(g1_pre_topc(A_8864,B_8865))
      | ~ m1_subset_1(B_8865,k1_zfmisc_1(k1_zfmisc_1(A_8864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62754,plain,(
    ! [A_45] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_45),u1_pre_topc(A_45)))
      | ~ l1_pre_topc(A_45) ) ),
    inference(resolution,[status(thm)],[c_64,c_62737])).

tff(c_80233,plain,
    ( v1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_80214,c_62754])).

tff(c_80333,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_80233])).

tff(c_80343,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56959,c_80333])).

tff(c_80347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_80343])).

tff(c_80349,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_80233])).

tff(c_56961,plain,(
    ! [A_8306] :
      ( v1_xboole_0(u1_pre_topc(A_8306))
      | ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8306))))
      | ~ l1_pre_topc(A_8306) ) ),
    inference(resolution,[status(thm)],[c_56949,c_18])).

tff(c_80679,plain,
    ( v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))))
    | ~ v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_80599,c_56961])).

tff(c_80700,plain,(
    v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80349,c_62543,c_62589,c_62589,c_80679])).

tff(c_80757,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_80700,c_62592])).

tff(c_80597,plain,(
    ! [A_12956,B_12957] :
      ( v1_funct_2('#skF_4',A_12956,B_12957)
      | A_12956 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80586,c_80376])).

tff(c_80760,plain,(
    ! [D_12980,A_12981,B_12982] :
      ( v5_pre_topc(D_12980,A_12981,g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982)))
      | ~ v5_pre_topc(D_12980,A_12981,B_12982)
      | ~ m1_subset_1(D_12980,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12981),u1_struct_0(g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982))))))
      | ~ v1_funct_2(D_12980,u1_struct_0(A_12981),u1_struct_0(g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982))))
      | ~ m1_subset_1(D_12980,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12981),u1_struct_0(B_12982))))
      | ~ v1_funct_2(D_12980,u1_struct_0(A_12981),u1_struct_0(B_12982))
      | ~ v1_funct_1(D_12980)
      | ~ l1_pre_topc(B_12982)
      | ~ v2_pre_topc(B_12982)
      | ~ l1_pre_topc(A_12981)
      | ~ v2_pre_topc(A_12981) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_80775,plain,(
    ! [D_12980,B_12982] :
      ( v5_pre_topc(D_12980,'#skF_2',g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982)))
      | ~ v5_pre_topc(D_12980,'#skF_2',B_12982)
      | ~ m1_subset_1(D_12980,k1_zfmisc_1(k2_zfmisc_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982))))))
      | ~ v1_funct_2(D_12980,u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982))))
      | ~ m1_subset_1(D_12980,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0(B_12982))))
      | ~ v1_funct_2(D_12980,u1_struct_0('#skF_2'),u1_struct_0(B_12982))
      | ~ v1_funct_1(D_12980)
      | ~ l1_pre_topc(B_12982)
      | ~ v2_pre_topc(B_12982)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77766,c_80760])).

tff(c_82246,plain,(
    ! [D_13117,B_13118] :
      ( v5_pre_topc(D_13117,'#skF_2',g1_pre_topc(u1_struct_0(B_13118),u1_pre_topc(B_13118)))
      | ~ v5_pre_topc(D_13117,'#skF_2',B_13118)
      | ~ v1_funct_2(D_13117,'#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_13118),u1_pre_topc(B_13118))))
      | ~ m1_subset_1(D_13117,'#skF_4')
      | ~ v1_funct_2(D_13117,'#skF_4',u1_struct_0(B_13118))
      | ~ v1_funct_1(D_13117)
      | ~ l1_pre_topc(B_13118)
      | ~ v2_pre_topc(B_13118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_77766,c_62589,c_62594,c_77766,c_77766,c_62589,c_62594,c_80775])).

tff(c_82261,plain,(
    ! [B_13118] :
      ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0(B_13118),u1_pre_topc(B_13118)))
      | ~ v5_pre_topc('#skF_4','#skF_2',B_13118)
      | ~ m1_subset_1('#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(B_13118))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_13118)
      | ~ v2_pre_topc(B_13118) ) ),
    inference(resolution,[status(thm)],[c_80597,c_82246])).

tff(c_82289,plain,(
    ! [B_13119] :
      ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0(B_13119),u1_pre_topc(B_13119)))
      | ~ v5_pre_topc('#skF_4','#skF_2',B_13119)
      | ~ l1_pre_topc(B_13119)
      | ~ v2_pre_topc(B_13119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80712,c_62588,c_82261])).

tff(c_82295,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_80599,c_82289])).

tff(c_82305,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80349,c_80757,c_82295])).

tff(c_82311,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_82305])).

tff(c_82349,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_82311])).

tff(c_82353,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_82349])).

tff(c_82355,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_82305])).

tff(c_80782,plain,(
    ! [A_12981,B_12982] :
      ( v5_pre_topc('#skF_4',A_12981,g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982)))
      | ~ v5_pre_topc('#skF_4',A_12981,B_12982)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_12981),u1_struct_0(g1_pre_topc(u1_struct_0(B_12982),u1_pre_topc(B_12982))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12981),u1_struct_0(B_12982))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_12981),u1_struct_0(B_12982))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_12982)
      | ~ v2_pre_topc(B_12982)
      | ~ l1_pre_topc(A_12981)
      | ~ v2_pre_topc(A_12981) ) ),
    inference(resolution,[status(thm)],[c_62593,c_80760])).

tff(c_82808,plain,(
    ! [A_13147,B_13148] :
      ( v5_pre_topc('#skF_4',A_13147,g1_pre_topc(u1_struct_0(B_13148),u1_pre_topc(B_13148)))
      | ~ v5_pre_topc('#skF_4',A_13147,B_13148)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_13147),u1_struct_0(g1_pre_topc(u1_struct_0(B_13148),u1_pre_topc(B_13148))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_13147),u1_struct_0(B_13148))
      | ~ l1_pre_topc(B_13148)
      | ~ v2_pre_topc(B_13148)
      | ~ l1_pre_topc(A_13147)
      | ~ v2_pre_topc(A_13147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_62593,c_80782])).

tff(c_82817,plain,(
    ! [B_13148] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_13148),u1_pre_topc(B_13148)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_13148)
      | ~ v1_funct_2('#skF_4','#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(B_13148),u1_pre_topc(B_13148))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))),u1_struct_0(B_13148))
      | ~ l1_pre_topc(B_13148)
      | ~ v2_pre_topc(B_13148)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80599,c_82808])).

tff(c_82848,plain,(
    ! [B_13149] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0(B_13149),u1_pre_topc(B_13149)))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),B_13149)
      | ~ l1_pre_topc(B_13149)
      | ~ v2_pre_topc(B_13149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82355,c_80349,c_80712,c_80599,c_80712,c_82817])).

tff(c_82863,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc(u1_struct_0('#skF_2'),'#skF_4'))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77819,c_82848])).

tff(c_82876,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),g1_pre_topc('#skF_4','#skF_4'))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_77766,c_82863])).

tff(c_82877,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc('#skF_1')),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_77859,c_82876])).

tff(c_82886,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_82606,c_82877])).

tff(c_82899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_77769,c_77766,c_56927,c_82886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.58/11.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.60/11.89  
% 22.60/11.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 22.60/11.89  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k1_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 22.60/11.89  
% 22.60/11.89  %Foreground sorts:
% 22.60/11.89  
% 22.60/11.89  
% 22.60/11.89  %Background operators:
% 22.60/11.89  
% 22.60/11.89  
% 22.60/11.89  %Foreground operators:
% 22.60/11.89  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 22.60/11.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.60/11.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.60/11.89  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 22.60/11.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.60/11.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.60/11.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.60/11.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.60/11.89  tff('#skF_2', type, '#skF_2': $i).
% 22.60/11.89  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.60/11.89  tff('#skF_3', type, '#skF_3': $i).
% 22.60/11.89  tff('#skF_1', type, '#skF_1': $i).
% 22.60/11.89  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 22.60/11.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 22.60/11.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.60/11.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.60/11.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.60/11.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.60/11.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.60/11.89  tff('#skF_4', type, '#skF_4': $i).
% 22.60/11.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.60/11.89  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 22.60/11.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.60/11.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 22.60/11.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.60/11.89  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.60/11.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.60/11.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.60/11.89  
% 23.01/11.99  tff(f_266, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 23.01/11.99  tff(f_170, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 23.01/11.99  tff(f_166, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 23.01/11.99  tff(f_85, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 23.01/11.99  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.01/11.99  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.01/11.99  tff(f_131, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 23.01/11.99  tff(f_103, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 23.01/11.99  tff(f_178, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 23.01/11.99  tff(f_207, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 23.01/11.99  tff(f_236, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 23.01/11.99  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.01/11.99  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 23.01/11.99  tff(f_160, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 23.01/11.99  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 23.01/11.99  tff(f_62, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 23.01/11.99  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 23.01/11.99  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.01/11.99  tff(f_143, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 23.01/11.99  tff(f_123, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 23.01/11.99  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 23.01/11.99  tff(f_68, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 23.01/11.99  tff(c_94, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_92, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_56949, plain, (![A_8306]: (m1_subset_1(u1_pre_topc(A_8306), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8306)))) | ~l1_pre_topc(A_8306))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_60, plain, (![A_43, B_44]: (l1_pre_topc(g1_pre_topc(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/11.99  tff(c_56959, plain, (![A_8306]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_8306), u1_pre_topc(A_8306))) | ~l1_pre_topc(A_8306))), inference(resolution, [status(thm)], [c_56949, c_60])).
% 23.01/11.99  tff(c_78, plain, ('#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_100, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_110, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_100])).
% 23.01/11.99  tff(c_40401, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 23.01/11.99  tff(c_98, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_96, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_111, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_86])).
% 23.01/11.99  tff(c_40532, plain, (![C_3848, B_3849, A_3850]: (v1_xboole_0(C_3848) | ~m1_subset_1(C_3848, k1_zfmisc_1(k2_zfmisc_1(B_3849, A_3850))) | ~v1_xboole_0(A_3850))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.01/11.99  tff(c_40554, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_111, c_40532])).
% 23.01/11.99  tff(c_40561, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_40554])).
% 23.01/11.99  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_201, plain, (![C_104, A_105, B_106]: (v1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 23.01/11.99  tff(c_220, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80, c_201])).
% 23.01/11.99  tff(c_40504, plain, (![C_3844, A_3845, B_3846]: (v4_relat_1(C_3844, A_3845) | ~m1_subset_1(C_3844, k1_zfmisc_1(k2_zfmisc_1(A_3845, B_3846))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/11.99  tff(c_40526, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_40504])).
% 23.01/11.99  tff(c_40646, plain, (![B_3878, A_3879]: (k1_relat_1(B_3878)=A_3879 | ~v1_partfun1(B_3878, A_3879) | ~v4_relat_1(B_3878, A_3879) | ~v1_relat_1(B_3878))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/11.99  tff(c_40658, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40526, c_40646])).
% 23.01/11.99  tff(c_40669, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_40658])).
% 23.01/11.99  tff(c_40695, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_40669])).
% 23.01/11.99  tff(c_88, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_107, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_88])).
% 23.01/11.99  tff(c_41054, plain, (![C_3940, A_3941, B_3942]: (v1_partfun1(C_3940, A_3941) | ~v1_funct_2(C_3940, A_3941, B_3942) | ~v1_funct_1(C_3940) | ~m1_subset_1(C_3940, k1_zfmisc_1(k2_zfmisc_1(A_3941, B_3942))) | v1_xboole_0(B_3942))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/11.99  tff(c_41060, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_111, c_41054])).
% 23.01/11.99  tff(c_41081, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_41060])).
% 23.01/11.99  tff(c_41083, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40561, c_40695, c_41081])).
% 23.01/11.99  tff(c_41084, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_40669])).
% 23.01/11.99  tff(c_41094, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_41084, c_107])).
% 23.01/11.99  tff(c_41093, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_41084, c_111])).
% 23.01/11.99  tff(c_40553, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_80, c_40532])).
% 23.01/11.99  tff(c_40565, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_40553])).
% 23.01/11.99  tff(c_82, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_41095, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_41084, c_82])).
% 23.01/11.99  tff(c_41092, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_41084, c_80])).
% 23.01/11.99  tff(c_41306, plain, (![C_3959, A_3960, B_3961]: (v1_partfun1(C_3959, A_3960) | ~v1_funct_2(C_3959, A_3960, B_3961) | ~v1_funct_1(C_3959) | ~m1_subset_1(C_3959, k1_zfmisc_1(k2_zfmisc_1(A_3960, B_3961))) | v1_xboole_0(B_3961))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/11.99  tff(c_41312, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_41092, c_41306])).
% 23.01/11.99  tff(c_41333, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_41095, c_41312])).
% 23.01/11.99  tff(c_41334, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_40565, c_41333])).
% 23.01/11.99  tff(c_40525, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_80, c_40504])).
% 23.01/11.99  tff(c_40655, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40525, c_40646])).
% 23.01/11.99  tff(c_40666, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_40655])).
% 23.01/11.99  tff(c_41692, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_41334, c_41084, c_41084, c_40666])).
% 23.01/11.99  tff(c_41700, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_41692, c_41095])).
% 23.01/11.99  tff(c_40423, plain, (![A_3829]: (m1_subset_1(u1_pre_topc(A_3829), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_3829)))) | ~l1_pre_topc(A_3829))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_40433, plain, (![A_3829]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_3829), u1_pre_topc(A_3829))) | ~l1_pre_topc(A_3829))), inference(resolution, [status(thm)], [c_40423, c_60])).
% 23.01/11.99  tff(c_66, plain, (![A_46]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_46), u1_pre_topc(A_46))) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_178])).
% 23.01/11.99  tff(c_41699, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_41692, c_41092])).
% 23.01/11.99  tff(c_106, plain, (v5_pre_topc('#skF_3', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_266])).
% 23.01/11.99  tff(c_108, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_106])).
% 23.01/11.99  tff(c_40451, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40401, c_108])).
% 23.01/11.99  tff(c_41091, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_41084, c_40451])).
% 23.01/11.99  tff(c_41629, plain, (![D_4008, A_4009, B_4010]: (v5_pre_topc(D_4008, A_4009, B_4010) | ~v5_pre_topc(D_4008, g1_pre_topc(u1_struct_0(A_4009), u1_pre_topc(A_4009)), B_4010) | ~m1_subset_1(D_4008, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4009), u1_pre_topc(A_4009))), u1_struct_0(B_4010)))) | ~v1_funct_2(D_4008, u1_struct_0(g1_pre_topc(u1_struct_0(A_4009), u1_pre_topc(A_4009))), u1_struct_0(B_4010)) | ~m1_subset_1(D_4008, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4009), u1_struct_0(B_4010)))) | ~v1_funct_2(D_4008, u1_struct_0(A_4009), u1_struct_0(B_4010)) | ~v1_funct_1(D_4008) | ~l1_pre_topc(B_4010) | ~v2_pre_topc(B_4010) | ~l1_pre_topc(A_4009) | ~v2_pre_topc(A_4009))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/11.99  tff(c_41632, plain, (![D_4008, B_4010]: (v5_pre_topc(D_4008, '#skF_1', B_4010) | ~v5_pre_topc(D_4008, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_4010) | ~m1_subset_1(D_4008, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_4010)))) | ~v1_funct_2(D_4008, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_4010)) | ~m1_subset_1(D_4008, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_4010)))) | ~v1_funct_2(D_4008, u1_struct_0('#skF_1'), u1_struct_0(B_4010)) | ~v1_funct_1(D_4008) | ~l1_pre_topc(B_4010) | ~v2_pre_topc(B_4010) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_41084, c_41629])).
% 23.01/11.99  tff(c_41645, plain, (![D_4008, B_4010]: (v5_pre_topc(D_4008, '#skF_1', B_4010) | ~v5_pre_topc(D_4008, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_4010) | ~m1_subset_1(D_4008, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_4010)))) | ~v1_funct_2(D_4008, u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_4010)) | ~m1_subset_1(D_4008, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_4010)))) | ~v1_funct_2(D_4008, k1_relat_1('#skF_4'), u1_struct_0(B_4010)) | ~v1_funct_1(D_4008) | ~l1_pre_topc(B_4010) | ~v2_pre_topc(B_4010))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_41084, c_41084, c_41084, c_41084, c_41632])).
% 23.01/11.99  tff(c_43965, plain, (![D_4205, B_4206]: (v5_pre_topc(D_4205, '#skF_1', B_4206) | ~v5_pre_topc(D_4205, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_4206) | ~m1_subset_1(D_4205, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_4206)))) | ~v1_funct_2(D_4205, k1_relat_1('#skF_4'), u1_struct_0(B_4206)) | ~m1_subset_1(D_4205, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_4206)))) | ~v1_funct_2(D_4205, k1_relat_1('#skF_4'), u1_struct_0(B_4206)) | ~v1_funct_1(D_4205) | ~l1_pre_topc(B_4206) | ~v2_pre_topc(B_4206))), inference(demodulation, [status(thm), theory('equality')], [c_41692, c_41692, c_41645])).
% 23.01/11.99  tff(c_43967, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_41699, c_43965])).
% 23.01/11.99  tff(c_43982, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_41700, c_41699, c_41091, c_43967])).
% 23.01/11.99  tff(c_44023, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_43982])).
% 23.01/11.99  tff(c_44026, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_44023])).
% 23.01/11.99  tff(c_44030, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_44026])).
% 23.01/11.99  tff(c_44031, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_43982])).
% 23.01/11.99  tff(c_44033, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_44031])).
% 23.01/11.99  tff(c_44036, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40433, c_44033])).
% 23.01/11.99  tff(c_44040, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_44036])).
% 23.01/11.99  tff(c_44041, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_44031])).
% 23.01/11.99  tff(c_43093, plain, (![D_4114, A_4115, B_4116]: (v5_pre_topc(D_4114, A_4115, B_4116) | ~v5_pre_topc(D_4114, A_4115, g1_pre_topc(u1_struct_0(B_4116), u1_pre_topc(B_4116))) | ~m1_subset_1(D_4114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4115), u1_struct_0(g1_pre_topc(u1_struct_0(B_4116), u1_pre_topc(B_4116)))))) | ~v1_funct_2(D_4114, u1_struct_0(A_4115), u1_struct_0(g1_pre_topc(u1_struct_0(B_4116), u1_pre_topc(B_4116)))) | ~m1_subset_1(D_4114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4115), u1_struct_0(B_4116)))) | ~v1_funct_2(D_4114, u1_struct_0(A_4115), u1_struct_0(B_4116)) | ~v1_funct_1(D_4114) | ~l1_pre_topc(B_4116) | ~v2_pre_topc(B_4116) | ~l1_pre_topc(A_4115) | ~v2_pre_topc(A_4115))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/11.99  tff(c_43102, plain, (![D_4114, B_4116]: (v5_pre_topc(D_4114, '#skF_1', B_4116) | ~v5_pre_topc(D_4114, '#skF_1', g1_pre_topc(u1_struct_0(B_4116), u1_pre_topc(B_4116))) | ~m1_subset_1(D_4114, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4116), u1_pre_topc(B_4116)))))) | ~v1_funct_2(D_4114, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4116), u1_pre_topc(B_4116)))) | ~m1_subset_1(D_4114, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_4116)))) | ~v1_funct_2(D_4114, u1_struct_0('#skF_1'), u1_struct_0(B_4116)) | ~v1_funct_1(D_4114) | ~l1_pre_topc(B_4116) | ~v2_pre_topc(B_4116) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_41084, c_43093])).
% 23.01/11.99  tff(c_44054, plain, (![D_4210, B_4211]: (v5_pre_topc(D_4210, '#skF_1', B_4211) | ~v5_pre_topc(D_4210, '#skF_1', g1_pre_topc(u1_struct_0(B_4211), u1_pre_topc(B_4211))) | ~m1_subset_1(D_4210, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4211), u1_pre_topc(B_4211)))))) | ~v1_funct_2(D_4210, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4211), u1_pre_topc(B_4211)))) | ~m1_subset_1(D_4210, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_4211)))) | ~v1_funct_2(D_4210, k1_relat_1('#skF_4'), u1_struct_0(B_4211)) | ~v1_funct_1(D_4210) | ~l1_pre_topc(B_4211) | ~v2_pre_topc(B_4211))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_41084, c_41084, c_41084, c_43102])).
% 23.01/11.99  tff(c_44060, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_41699, c_44054])).
% 23.01/11.99  tff(c_44079, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_41094, c_41093, c_41700, c_44041, c_44060])).
% 23.01/11.99  tff(c_44081, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40401, c_44079])).
% 23.01/11.99  tff(c_44082, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_40553])).
% 23.01/11.99  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 23.01/11.99  tff(c_141, plain, (![B_91, A_92]: (~v1_xboole_0(B_91) | B_91=A_92 | ~v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_34])).
% 23.01/11.99  tff(c_144, plain, (![A_92]: (k1_xboole_0=A_92 | ~v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_2, c_141])).
% 23.01/11.99  tff(c_44094, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44082, c_144])).
% 23.01/11.99  tff(c_19022, plain, (![A_1832]: (m1_subset_1(u1_pre_topc(A_1832), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1832)))) | ~l1_pre_topc(A_1832))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_19036, plain, (![A_1832]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1832), u1_pre_topc(A_1832))) | ~l1_pre_topc(A_1832))), inference(resolution, [status(thm)], [c_19022, c_60])).
% 23.01/11.99  tff(c_19039, plain, (![C_1833, A_1834, B_1835]: (v4_relat_1(C_1833, A_1834) | ~m1_subset_1(C_1833, k1_zfmisc_1(k2_zfmisc_1(A_1834, B_1835))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/11.99  tff(c_19061, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_19039])).
% 23.01/11.99  tff(c_19175, plain, (![B_1858, A_1859]: (k1_relat_1(B_1858)=A_1859 | ~v1_partfun1(B_1858, A_1859) | ~v4_relat_1(B_1858, A_1859) | ~v1_relat_1(B_1858))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/11.99  tff(c_19181, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_19061, c_19175])).
% 23.01/11.99  tff(c_19190, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_19181])).
% 23.01/11.99  tff(c_19200, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_19190])).
% 23.01/11.99  tff(c_19313, plain, (![B_1894, C_1895, A_1896]: (k1_xboole_0=B_1894 | v1_partfun1(C_1895, A_1896) | ~v1_funct_2(C_1895, A_1896, B_1894) | ~m1_subset_1(C_1895, k1_zfmisc_1(k2_zfmisc_1(A_1896, B_1894))) | ~v1_funct_1(C_1895))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.01/11.99  tff(c_19319, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_19313])).
% 23.01/11.99  tff(c_19340, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_19319])).
% 23.01/11.99  tff(c_19341, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_19200, c_19340])).
% 23.01/11.99  tff(c_19100, plain, (![C_1846, B_1847, A_1848]: (v1_xboole_0(C_1846) | ~m1_subset_1(C_1846, k1_zfmisc_1(k2_zfmisc_1(B_1847, A_1848))) | ~v1_xboole_0(A_1848))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.01/11.99  tff(c_19122, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_111, c_19100])).
% 23.01/11.99  tff(c_19128, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_19122])).
% 23.01/11.99  tff(c_19351, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_19341, c_19128])).
% 23.01/11.99  tff(c_19363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_19351])).
% 23.01/11.99  tff(c_19364, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_19190])).
% 23.01/11.99  tff(c_243, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_108])).
% 23.01/11.99  tff(c_8, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.01/11.99  tff(c_388, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 23.01/11.99  tff(c_323, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/11.99  tff(c_345, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_323])).
% 23.01/11.99  tff(c_440, plain, (![B_145, A_146]: (k1_relat_1(B_145)=A_146 | ~v1_partfun1(B_145, A_146) | ~v4_relat_1(B_145, A_146) | ~v1_relat_1(B_145))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/11.99  tff(c_446, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_345, c_440])).
% 23.01/11.99  tff(c_455, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_446])).
% 23.01/11.99  tff(c_479, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_455])).
% 23.01/11.99  tff(c_640, plain, (![B_190, C_191, A_192]: (k1_xboole_0=B_190 | v1_partfun1(C_191, A_192) | ~v1_funct_2(C_191, A_192, B_190) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_190))) | ~v1_funct_1(C_191))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.01/11.99  tff(c_646, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_640])).
% 23.01/11.99  tff(c_666, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_646])).
% 23.01/11.99  tff(c_667, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_479, c_666])).
% 23.01/11.99  tff(c_412, plain, (![C_142, B_143, A_144]: (v1_xboole_0(C_142) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(B_143, A_144))) | ~v1_xboole_0(A_144))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.01/11.99  tff(c_434, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_111, c_412])).
% 23.01/11.99  tff(c_459, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_434])).
% 23.01/11.99  tff(c_677, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_667, c_459])).
% 23.01/11.99  tff(c_688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_677])).
% 23.01/11.99  tff(c_689, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_455])).
% 23.01/11.99  tff(c_696, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_107])).
% 23.01/11.99  tff(c_695, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_111])).
% 23.01/11.99  tff(c_697, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_82])).
% 23.01/11.99  tff(c_694, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_80])).
% 23.01/11.99  tff(c_935, plain, (![B_213, C_214, A_215]: (k1_xboole_0=B_213 | v1_partfun1(C_214, A_215) | ~v1_funct_2(C_214, A_215, B_213) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_213))) | ~v1_funct_1(C_214))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.01/11.99  tff(c_938, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_694, c_935])).
% 23.01/11.99  tff(c_958, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_697, c_938])).
% 23.01/11.99  tff(c_1061, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_958])).
% 23.01/11.99  tff(c_344, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_80, c_323])).
% 23.01/11.99  tff(c_443, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_344, c_440])).
% 23.01/11.99  tff(c_452, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_443])).
% 23.01/11.99  tff(c_1063, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_689, c_689, c_452])).
% 23.01/11.99  tff(c_1069, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_697])).
% 23.01/11.99  tff(c_293, plain, (![A_119]: (m1_subset_1(u1_pre_topc(A_119), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_119)))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_303, plain, (![A_119]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_119), u1_pre_topc(A_119))) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_293, c_60])).
% 23.01/11.99  tff(c_829, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_243])).
% 23.01/11.99  tff(c_1067, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_694])).
% 23.01/11.99  tff(c_2058, plain, (![D_298, A_299, B_300]: (v5_pre_topc(D_298, A_299, B_300) | ~v5_pre_topc(D_298, g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299)), B_300) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299))), u1_struct_0(B_300)))) | ~v1_funct_2(D_298, u1_struct_0(g1_pre_topc(u1_struct_0(A_299), u1_pre_topc(A_299))), u1_struct_0(B_300)) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_299), u1_struct_0(B_300)))) | ~v1_funct_2(D_298, u1_struct_0(A_299), u1_struct_0(B_300)) | ~v1_funct_1(D_298) | ~l1_pre_topc(B_300) | ~v2_pre_topc(B_300) | ~l1_pre_topc(A_299) | ~v2_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/11.99  tff(c_2067, plain, (![D_298, B_300]: (v5_pre_topc(D_298, '#skF_1', B_300) | ~v5_pre_topc(D_298, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_300) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_300)))) | ~v1_funct_2(D_298, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_300)) | ~m1_subset_1(D_298, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_300)))) | ~v1_funct_2(D_298, u1_struct_0('#skF_1'), u1_struct_0(B_300)) | ~v1_funct_1(D_298) | ~l1_pre_topc(B_300) | ~v2_pre_topc(B_300) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_689, c_2058])).
% 23.01/11.99  tff(c_2579, plain, (![D_343, B_344]: (v5_pre_topc(D_343, '#skF_1', B_344) | ~v5_pre_topc(D_343, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_344) | ~m1_subset_1(D_343, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_344)))) | ~v1_funct_2(D_343, k1_relat_1('#skF_4'), u1_struct_0(B_344)) | ~v1_funct_1(D_343) | ~l1_pre_topc(B_344) | ~v2_pre_topc(B_344))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_689, c_689, c_1063, c_689, c_1063, c_689, c_2067])).
% 23.01/11.99  tff(c_2582, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_1067, c_2579])).
% 23.01/11.99  tff(c_2602, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1069, c_829, c_2582])).
% 23.01/11.99  tff(c_2641, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_2602])).
% 23.01/11.99  tff(c_2644, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_2641])).
% 23.01/11.99  tff(c_2648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_2644])).
% 23.01/11.99  tff(c_2649, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_2602])).
% 23.01/11.99  tff(c_2651, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_2649])).
% 23.01/11.99  tff(c_2654, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_303, c_2651])).
% 23.01/11.99  tff(c_2658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_2654])).
% 23.01/11.99  tff(c_2659, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_2649])).
% 23.01/11.99  tff(c_2169, plain, (![D_308, A_309, B_310]: (v5_pre_topc(D_308, A_309, B_310) | ~v5_pre_topc(D_308, A_309, g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310))) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_309), u1_struct_0(g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310)))))) | ~v1_funct_2(D_308, u1_struct_0(A_309), u1_struct_0(g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310)))) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_309), u1_struct_0(B_310)))) | ~v1_funct_2(D_308, u1_struct_0(A_309), u1_struct_0(B_310)) | ~v1_funct_1(D_308) | ~l1_pre_topc(B_310) | ~v2_pre_topc(B_310) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/11.99  tff(c_2178, plain, (![D_308, B_310]: (v5_pre_topc(D_308, '#skF_1', B_310) | ~v5_pre_topc(D_308, '#skF_1', g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310))) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310)))))) | ~v1_funct_2(D_308, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_310), u1_pre_topc(B_310)))) | ~m1_subset_1(D_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_310)))) | ~v1_funct_2(D_308, u1_struct_0('#skF_1'), u1_struct_0(B_310)) | ~v1_funct_1(D_308) | ~l1_pre_topc(B_310) | ~v2_pre_topc(B_310) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_689, c_2169])).
% 23.01/11.99  tff(c_2801, plain, (![D_359, B_360]: (v5_pre_topc(D_359, '#skF_1', B_360) | ~v5_pre_topc(D_359, '#skF_1', g1_pre_topc(u1_struct_0(B_360), u1_pre_topc(B_360))) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_360), u1_pre_topc(B_360)))))) | ~v1_funct_2(D_359, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_360), u1_pre_topc(B_360)))) | ~m1_subset_1(D_359, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_360)))) | ~v1_funct_2(D_359, k1_relat_1('#skF_4'), u1_struct_0(B_360)) | ~v1_funct_1(D_359) | ~l1_pre_topc(B_360) | ~v2_pre_topc(B_360))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_689, c_689, c_689, c_2178])).
% 23.01/11.99  tff(c_2807, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1067, c_2801])).
% 23.01/11.99  tff(c_2826, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_696, c_695, c_1069, c_2659, c_2807])).
% 23.01/11.99  tff(c_2828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_2826])).
% 23.01/11.99  tff(c_2829, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_958])).
% 23.01/11.99  tff(c_22, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_62])).
% 23.01/11.99  tff(c_198, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_80, c_22])).
% 23.01/11.99  tff(c_786, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_198])).
% 23.01/11.99  tff(c_787, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(splitLeft, [status(thm)], [c_786])).
% 23.01/11.99  tff(c_2831, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2829, c_787])).
% 23.01/11.99  tff(c_2839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_2831])).
% 23.01/11.99  tff(c_2840, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_786])).
% 23.01/11.99  tff(c_2847, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2840, c_144])).
% 23.01/11.99  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.01/11.99  tff(c_2866, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_10])).
% 23.01/11.99  tff(c_20, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.01/11.99  tff(c_741, plain, (![A_193, B_194, C_195]: (k1_relset_1(A_193, B_194, C_195)=k1_relat_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/11.99  tff(c_757, plain, (![A_193, B_194]: (k1_relset_1(A_193, B_194, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_741])).
% 23.01/11.99  tff(c_2849, plain, (![A_193, B_194]: (k1_relset_1(A_193, B_194, '#skF_4')=k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_757])).
% 23.01/11.99  tff(c_2865, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_20])).
% 23.01/11.99  tff(c_3104, plain, (![C_379, A_380, B_381]: (v1_funct_2(C_379, A_380, B_381) | k1_relset_1(A_380, B_381, C_379)!=A_380 | ~m1_subset_1(C_379, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))) | ~v1_funct_1(C_379))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/11.99  tff(c_3114, plain, (![A_380, B_381]: (v1_funct_2('#skF_4', A_380, B_381) | k1_relset_1(A_380, B_381, '#skF_4')!=A_380 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2865, c_3104])).
% 23.01/11.99  tff(c_3121, plain, (![A_380, B_381]: (v1_funct_2('#skF_4', A_380, B_381) | k1_relat_1('#skF_4')!=A_380)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2849, c_3114])).
% 23.01/11.99  tff(c_3885, plain, (![C_430, A_431, B_432]: (~v1_xboole_0(C_430) | ~v1_funct_2(C_430, A_431, B_432) | ~v1_funct_1(C_430) | ~m1_subset_1(C_430, k1_zfmisc_1(k2_zfmisc_1(A_431, B_432))) | v1_xboole_0(B_432) | v1_xboole_0(A_431))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/11.99  tff(c_3895, plain, (![A_431, B_432]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_431, B_432) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_432) | v1_xboole_0(A_431))), inference(resolution, [status(thm)], [c_2865, c_3885])).
% 23.01/11.99  tff(c_3920, plain, (![A_435, B_436]: (~v1_funct_2('#skF_4', A_435, B_436) | v1_xboole_0(B_436) | v1_xboole_0(A_435))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2840, c_3895])).
% 23.01/11.99  tff(c_3924, plain, (![B_381, A_380]: (v1_xboole_0(B_381) | v1_xboole_0(A_380) | k1_relat_1('#skF_4')!=A_380)), inference(resolution, [status(thm)], [c_3121, c_3920])).
% 23.01/11.99  tff(c_3927, plain, (![A_437]: (v1_xboole_0(A_437) | k1_relat_1('#skF_4')!=A_437)), inference(splitLeft, [status(thm)], [c_3924])).
% 23.01/11.99  tff(c_4, plain, (![B_2, A_1]: (~v1_xboole_0(B_2) | B_2=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 23.01/11.99  tff(c_2848, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_2840, c_4])).
% 23.01/11.99  tff(c_3987, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3927, c_2848])).
% 23.01/11.99  tff(c_3877, plain, (![A_428, B_429]: (v1_funct_2('#skF_4', A_428, B_429) | k1_relat_1('#skF_4')!=A_428)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2849, c_3114])).
% 23.01/11.99  tff(c_56, plain, (![C_42, B_41]: (v1_partfun1(C_42, k1_xboole_0) | ~v1_funct_2(C_42, k1_xboole_0, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_41))) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.01/11.99  tff(c_113, plain, (![C_42, B_41]: (v1_partfun1(C_42, k1_xboole_0) | ~v1_funct_2(C_42, k1_xboole_0, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_56])).
% 23.01/11.99  tff(c_3064, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_2847, c_2847, c_113])).
% 23.01/11.99  tff(c_3880, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_3877, c_3064])).
% 23.01/11.99  tff(c_3883, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2865, c_3880])).
% 23.01/11.99  tff(c_3884, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_3883])).
% 23.01/11.99  tff(c_4001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3987, c_3884])).
% 23.01/11.99  tff(c_4002, plain, (![B_381]: (v1_xboole_0(B_381))), inference(splitRight, [status(thm)], [c_3924])).
% 23.01/11.99  tff(c_16, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.01/11.99  tff(c_230, plain, (![C_109]: (v1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_201])).
% 23.01/11.99  tff(c_239, plain, (![B_6]: (v1_relat_1(B_6) | ~v1_xboole_0(B_6) | ~v1_xboole_0(k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_16, c_230])).
% 23.01/11.99  tff(c_242, plain, (~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_239])).
% 23.01/11.99  tff(c_2860, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2847, c_242])).
% 23.01/11.99  tff(c_4035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4002, c_2860])).
% 23.01/11.99  tff(c_4037, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_3883])).
% 23.01/11.99  tff(c_179, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_111, c_22])).
% 23.01/11.99  tff(c_244, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_179])).
% 23.01/11.99  tff(c_693, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_689, c_244])).
% 23.01/11.99  tff(c_4048, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4037, c_693])).
% 23.01/11.99  tff(c_4053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2840, c_2866, c_4048])).
% 23.01/11.99  tff(c_4054, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_434])).
% 23.01/11.99  tff(c_4061, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4054, c_144])).
% 23.01/11.99  tff(c_4078, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4061, c_4061, c_8])).
% 23.01/11.99  tff(c_4055, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_434])).
% 23.01/11.99  tff(c_4123, plain, (![A_446]: (A_446='#skF_4' | ~v1_xboole_0(A_446))), inference(resolution, [status(thm)], [c_4054, c_4])).
% 23.01/11.99  tff(c_4130, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_4055, c_4123])).
% 23.01/11.99  tff(c_4134, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4130, c_244])).
% 23.01/11.99  tff(c_4286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4054, c_4078, c_4134])).
% 23.01/11.99  tff(c_4287, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_110])).
% 23.01/11.99  tff(c_4472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_4287])).
% 23.01/11.99  tff(c_4474, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_179])).
% 23.01/11.99  tff(c_4473, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_179])).
% 23.01/11.99  tff(c_4481, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4473, c_4])).
% 23.01/11.99  tff(c_18482, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_4474, c_4481])).
% 23.01/11.99  tff(c_4480, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4473, c_144])).
% 23.01/11.99  tff(c_6, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.01/11.99  tff(c_18537, plain, (![B_1756, A_1757]: (B_1756='#skF_4' | A_1757='#skF_4' | k2_zfmisc_1(A_1757, B_1756)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_4480, c_4480, c_6])).
% 23.01/11.99  tff(c_18547, plain, (u1_struct_0('#skF_2')='#skF_4' | u1_struct_0('#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_18482, c_18537])).
% 23.01/11.99  tff(c_18552, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitLeft, [status(thm)], [c_18547])).
% 23.01/11.99  tff(c_18672, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18552, c_243])).
% 23.01/11.99  tff(c_4482, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_110])).
% 23.01/11.99  tff(c_64, plain, (![A_45]: (m1_subset_1(u1_pre_topc(A_45), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45)))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_4695, plain, (![A_505, B_506]: (l1_pre_topc(g1_pre_topc(A_505, B_506)) | ~m1_subset_1(B_506, k1_zfmisc_1(k1_zfmisc_1(A_505))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/11.99  tff(c_4711, plain, (![A_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_45), u1_pre_topc(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_4695])).
% 23.01/11.99  tff(c_4487, plain, (![A_92]: (A_92='#skF_4' | ~v1_xboole_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_144])).
% 23.01/11.99  tff(c_4567, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_4474, c_4487])).
% 23.01/11.99  tff(c_4634, plain, (![B_501, A_502]: (B_501='#skF_4' | A_502='#skF_4' | k2_zfmisc_1(A_502, B_501)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_4480, c_4480, c_6])).
% 23.01/11.99  tff(c_4644, plain, (u1_struct_0('#skF_2')='#skF_4' | u1_struct_0('#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4567, c_4634])).
% 23.01/11.99  tff(c_4649, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitLeft, [status(thm)], [c_4644])).
% 23.01/11.99  tff(c_4806, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4649, c_243])).
% 23.01/11.99  tff(c_4841, plain, (![A_530]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_530), u1_pre_topc(A_530))) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530))), inference(cnfTransformation, [status(thm)], [f_178])).
% 23.01/11.99  tff(c_4844, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4649, c_4841])).
% 23.01/11.99  tff(c_4846, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_4844])).
% 23.01/11.99  tff(c_4658, plain, (![A_503]: (m1_subset_1(u1_pre_topc(A_503), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_503)))) | ~l1_pre_topc(A_503))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_4670, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4649, c_4658])).
% 23.01/11.99  tff(c_4675, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_4670])).
% 23.01/11.99  tff(c_4710, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_4675, c_4695])).
% 23.01/11.99  tff(c_4488, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_20])).
% 23.01/11.99  tff(c_4651, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4649, c_107])).
% 23.01/11.99  tff(c_10828, plain, (![C_1047, B_1048]: (v1_partfun1(C_1047, '#skF_4') | ~v1_funct_2(C_1047, '#skF_4', B_1048) | ~m1_subset_1(C_1047, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1047))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_4480, c_4480, c_113])).
% 23.01/11.99  tff(c_10833, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_4651, c_10828])).
% 23.01/11.99  tff(c_10839, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_10833])).
% 23.01/11.99  tff(c_4714, plain, (![C_507, A_508, B_509]: (v4_relat_1(C_507, A_508) | ~m1_subset_1(C_507, k1_zfmisc_1(k2_zfmisc_1(A_508, B_509))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/11.99  tff(c_4729, plain, (![A_508]: (v4_relat_1('#skF_4', A_508))), inference(resolution, [status(thm)], [c_4488, c_4714])).
% 23.01/11.99  tff(c_10709, plain, (![B_1018, A_1019]: (k1_relat_1(B_1018)=A_1019 | ~v1_partfun1(B_1018, A_1019) | ~v4_relat_1(B_1018, A_1019) | ~v1_relat_1(B_1018))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/11.99  tff(c_10712, plain, (![A_508]: (k1_relat_1('#skF_4')=A_508 | ~v1_partfun1('#skF_4', A_508) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4729, c_10709])).
% 23.01/11.99  tff(c_10715, plain, (![A_508]: (k1_relat_1('#skF_4')=A_508 | ~v1_partfun1('#skF_4', A_508))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_10712])).
% 23.01/11.99  tff(c_10843, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_10839, c_10715])).
% 23.01/11.99  tff(c_10730, plain, (![A_1024, B_1025, C_1026]: (k1_relset_1(A_1024, B_1025, C_1026)=k1_relat_1(C_1026) | ~m1_subset_1(C_1026, k1_zfmisc_1(k2_zfmisc_1(A_1024, B_1025))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/11.99  tff(c_10745, plain, (![A_1024, B_1025]: (k1_relset_1(A_1024, B_1025, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_10730])).
% 23.01/11.99  tff(c_10774, plain, (![C_1033, A_1034, B_1035]: (v1_funct_2(C_1033, A_1034, B_1035) | k1_relset_1(A_1034, B_1035, C_1033)!=A_1034 | ~m1_subset_1(C_1033, k1_zfmisc_1(k2_zfmisc_1(A_1034, B_1035))) | ~v1_funct_1(C_1033))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/11.99  tff(c_10784, plain, (![A_1034, B_1035]: (v1_funct_2('#skF_4', A_1034, B_1035) | k1_relset_1(A_1034, B_1035, '#skF_4')!=A_1034 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_10774])).
% 23.01/11.99  tff(c_10791, plain, (![A_1034, B_1035]: (v1_funct_2('#skF_4', A_1034, B_1035) | k1_relat_1('#skF_4')!=A_1034)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10745, c_10784])).
% 23.01/11.99  tff(c_10893, plain, (![B_1035]: (v1_funct_2('#skF_4', '#skF_4', B_1035))), inference(demodulation, [status(thm), theory('equality')], [c_10843, c_10791])).
% 23.01/11.99  tff(c_4652, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_4649, c_82])).
% 23.01/11.99  tff(c_58, plain, (![B_41, C_42, A_40]: (k1_xboole_0=B_41 | v1_partfun1(C_42, A_40) | ~v1_funct_2(C_42, A_40, B_41) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))) | ~v1_funct_1(C_42))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.01/11.99  tff(c_10913, plain, (![B_1059, C_1060, A_1061]: (B_1059='#skF_4' | v1_partfun1(C_1060, A_1061) | ~v1_funct_2(C_1060, A_1061, B_1059) | ~m1_subset_1(C_1060, k1_zfmisc_1(k2_zfmisc_1(A_1061, B_1059))) | ~v1_funct_1(C_1060))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_58])).
% 23.01/11.99  tff(c_10923, plain, (![B_1059, A_1061]: (B_1059='#skF_4' | v1_partfun1('#skF_4', A_1061) | ~v1_funct_2('#skF_4', A_1061, B_1059) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_10913])).
% 23.01/11.99  tff(c_10940, plain, (![B_1063, A_1064]: (B_1063='#skF_4' | v1_partfun1('#skF_4', A_1064) | ~v1_funct_2('#skF_4', A_1064, B_1063))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10923])).
% 23.01/11.99  tff(c_10948, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_4652, c_10940])).
% 23.01/11.99  tff(c_10953, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_10948])).
% 23.01/11.99  tff(c_10846, plain, (![A_508]: (A_508='#skF_4' | ~v1_partfun1('#skF_4', A_508))), inference(demodulation, [status(thm), theory('equality')], [c_10843, c_10715])).
% 23.01/11.99  tff(c_10957, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_10953, c_10846])).
% 23.01/11.99  tff(c_11451, plain, (![D_1119, A_1120, B_1121]: (v5_pre_topc(D_1119, A_1120, B_1121) | ~v5_pre_topc(D_1119, A_1120, g1_pre_topc(u1_struct_0(B_1121), u1_pre_topc(B_1121))) | ~m1_subset_1(D_1119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1120), u1_struct_0(g1_pre_topc(u1_struct_0(B_1121), u1_pre_topc(B_1121)))))) | ~v1_funct_2(D_1119, u1_struct_0(A_1120), u1_struct_0(g1_pre_topc(u1_struct_0(B_1121), u1_pre_topc(B_1121)))) | ~m1_subset_1(D_1119, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1120), u1_struct_0(B_1121)))) | ~v1_funct_2(D_1119, u1_struct_0(A_1120), u1_struct_0(B_1121)) | ~v1_funct_1(D_1119) | ~l1_pre_topc(B_1121) | ~v2_pre_topc(B_1121) | ~l1_pre_topc(A_1120) | ~v2_pre_topc(A_1120))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/11.99  tff(c_11470, plain, (![A_1120, B_1121]: (v5_pre_topc('#skF_4', A_1120, B_1121) | ~v5_pre_topc('#skF_4', A_1120, g1_pre_topc(u1_struct_0(B_1121), u1_pre_topc(B_1121))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1120), u1_struct_0(g1_pre_topc(u1_struct_0(B_1121), u1_pre_topc(B_1121)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1120), u1_struct_0(B_1121)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1120), u1_struct_0(B_1121)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1121) | ~v2_pre_topc(B_1121) | ~l1_pre_topc(A_1120) | ~v2_pre_topc(A_1120))), inference(resolution, [status(thm)], [c_4488, c_11451])).
% 23.01/11.99  tff(c_11660, plain, (![A_1138, B_1139]: (v5_pre_topc('#skF_4', A_1138, B_1139) | ~v5_pre_topc('#skF_4', A_1138, g1_pre_topc(u1_struct_0(B_1139), u1_pre_topc(B_1139))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1138), u1_struct_0(g1_pre_topc(u1_struct_0(B_1139), u1_pre_topc(B_1139)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1138), u1_struct_0(B_1139)) | ~l1_pre_topc(B_1139) | ~v2_pre_topc(B_1139) | ~l1_pre_topc(A_1138) | ~v2_pre_topc(A_1138))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_11470])).
% 23.01/11.99  tff(c_11666, plain, (![B_1139]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1139) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_1139), u1_pre_topc(B_1139))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1139), u1_pre_topc(B_1139)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1139)) | ~l1_pre_topc(B_1139) | ~v2_pre_topc(B_1139) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_10957, c_11660])).
% 23.01/11.99  tff(c_11732, plain, (![B_1142]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1142) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_1142), u1_pre_topc(B_1142))) | ~l1_pre_topc(B_1142) | ~v2_pre_topc(B_1142))), inference(demodulation, [status(thm), theory('equality')], [c_4846, c_4710, c_10893, c_10957, c_10893, c_11666])).
% 23.01/11.99  tff(c_11748, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4806, c_11732])).
% 23.01/11.99  tff(c_11764, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_11748])).
% 23.01/11.99  tff(c_11089, plain, (![D_1078, A_1079, B_1080]: (v5_pre_topc(D_1078, A_1079, B_1080) | ~v5_pre_topc(D_1078, g1_pre_topc(u1_struct_0(A_1079), u1_pre_topc(A_1079)), B_1080) | ~m1_subset_1(D_1078, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1079), u1_pre_topc(A_1079))), u1_struct_0(B_1080)))) | ~v1_funct_2(D_1078, u1_struct_0(g1_pre_topc(u1_struct_0(A_1079), u1_pre_topc(A_1079))), u1_struct_0(B_1080)) | ~m1_subset_1(D_1078, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1079), u1_struct_0(B_1080)))) | ~v1_funct_2(D_1078, u1_struct_0(A_1079), u1_struct_0(B_1080)) | ~v1_funct_1(D_1078) | ~l1_pre_topc(B_1080) | ~v2_pre_topc(B_1080) | ~l1_pre_topc(A_1079) | ~v2_pre_topc(A_1079))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/11.99  tff(c_11105, plain, (![A_1079, B_1080]: (v5_pre_topc('#skF_4', A_1079, B_1080) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1079), u1_pre_topc(A_1079)), B_1080) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1079), u1_pre_topc(A_1079))), u1_struct_0(B_1080)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1079), u1_struct_0(B_1080)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1079), u1_struct_0(B_1080)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1080) | ~v2_pre_topc(B_1080) | ~l1_pre_topc(A_1079) | ~v2_pre_topc(A_1079))), inference(resolution, [status(thm)], [c_4488, c_11089])).
% 23.01/11.99  tff(c_11768, plain, (![A_1143, B_1144]: (v5_pre_topc('#skF_4', A_1143, B_1144) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1143), u1_pre_topc(A_1143)), B_1144) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1143), u1_pre_topc(A_1143))), u1_struct_0(B_1144)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1143), u1_struct_0(B_1144)) | ~l1_pre_topc(B_1144) | ~v2_pre_topc(B_1144) | ~l1_pre_topc(A_1143) | ~v2_pre_topc(A_1143))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_11105])).
% 23.01/11.99  tff(c_11783, plain, (![B_1144]: (v5_pre_topc('#skF_4', '#skF_1', B_1144) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1144) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1144)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1144)) | ~l1_pre_topc(B_1144) | ~v2_pre_topc(B_1144) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4649, c_11768])).
% 23.01/11.99  tff(c_11820, plain, (![B_1146]: (v5_pre_topc('#skF_4', '#skF_1', B_1146) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1146) | ~l1_pre_topc(B_1146) | ~v2_pre_topc(B_1146))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_10893, c_4649, c_10893, c_10957, c_4649, c_11783])).
% 23.01/11.99  tff(c_11823, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_11764, c_11820])).
% 23.01/11.99  tff(c_11840, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_11823])).
% 23.01/11.99  tff(c_11842, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4482, c_11840])).
% 23.01/11.99  tff(c_11843, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_10948])).
% 23.01/11.99  tff(c_62, plain, (![A_43, B_44]: (v1_pre_topc(g1_pre_topc(A_43, B_44)) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_43))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/11.99  tff(c_4671, plain, (![A_503]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_503), u1_pre_topc(A_503))) | ~l1_pre_topc(A_503))), inference(resolution, [status(thm)], [c_4658, c_62])).
% 23.01/11.99  tff(c_11866, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11843, c_4671])).
% 23.01/11.99  tff(c_12114, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_11866])).
% 23.01/11.99  tff(c_12120, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4711, c_12114])).
% 23.01/11.99  tff(c_12125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_12120])).
% 23.01/11.99  tff(c_12127, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_11866])).
% 23.01/11.99  tff(c_11857, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11843, c_66])).
% 23.01/11.99  tff(c_12327, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12127, c_11857])).
% 23.01/11.99  tff(c_12328, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_12327])).
% 23.01/11.99  tff(c_12331, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_12328])).
% 23.01/11.99  tff(c_12335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12331])).
% 23.01/11.99  tff(c_12337, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_12327])).
% 23.01/11.99  tff(c_14, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.01/11.99  tff(c_11869, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11843, c_64])).
% 23.01/11.99  tff(c_12202, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12127, c_11869])).
% 23.01/11.99  tff(c_24, plain, (![A_11, C_13, B_12]: (m1_subset_1(A_11, C_13) | ~m1_subset_1(B_12, k1_zfmisc_1(C_13)) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.01/11.99  tff(c_12224, plain, (![A_1190]: (m1_subset_1(A_1190, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_1190, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_12202, c_24])).
% 23.01/11.99  tff(c_12229, plain, (![B_6]: (m1_subset_1(B_6, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_6, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_14, c_12224])).
% 23.01/11.99  tff(c_12312, plain, (v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_12229])).
% 23.01/11.99  tff(c_12324, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(resolution, [status(thm)], [c_12312, c_4487])).
% 23.01/11.99  tff(c_12272, plain, (![D_1199, A_1200, B_1201]: (v5_pre_topc(D_1199, A_1200, g1_pre_topc(u1_struct_0(B_1201), u1_pre_topc(B_1201))) | ~v5_pre_topc(D_1199, A_1200, B_1201) | ~m1_subset_1(D_1199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1200), u1_struct_0(g1_pre_topc(u1_struct_0(B_1201), u1_pre_topc(B_1201)))))) | ~v1_funct_2(D_1199, u1_struct_0(A_1200), u1_struct_0(g1_pre_topc(u1_struct_0(B_1201), u1_pre_topc(B_1201)))) | ~m1_subset_1(D_1199, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1200), u1_struct_0(B_1201)))) | ~v1_funct_2(D_1199, u1_struct_0(A_1200), u1_struct_0(B_1201)) | ~v1_funct_1(D_1199) | ~l1_pre_topc(B_1201) | ~v2_pre_topc(B_1201) | ~l1_pre_topc(A_1200) | ~v2_pre_topc(A_1200))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/11.99  tff(c_12291, plain, (![A_1200, B_1201]: (v5_pre_topc('#skF_4', A_1200, g1_pre_topc(u1_struct_0(B_1201), u1_pre_topc(B_1201))) | ~v5_pre_topc('#skF_4', A_1200, B_1201) | ~v1_funct_2('#skF_4', u1_struct_0(A_1200), u1_struct_0(g1_pre_topc(u1_struct_0(B_1201), u1_pre_topc(B_1201)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1200), u1_struct_0(B_1201)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1200), u1_struct_0(B_1201)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1201) | ~v2_pre_topc(B_1201) | ~l1_pre_topc(A_1200) | ~v2_pre_topc(A_1200))), inference(resolution, [status(thm)], [c_4488, c_12272])).
% 23.01/11.99  tff(c_12520, plain, (![A_1210, B_1211]: (v5_pre_topc('#skF_4', A_1210, g1_pre_topc(u1_struct_0(B_1211), u1_pre_topc(B_1211))) | ~v5_pre_topc('#skF_4', A_1210, B_1211) | ~v1_funct_2('#skF_4', u1_struct_0(A_1210), u1_struct_0(g1_pre_topc(u1_struct_0(B_1211), u1_pre_topc(B_1211)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1210), u1_struct_0(B_1211)) | ~l1_pre_topc(B_1211) | ~v2_pre_topc(B_1211) | ~l1_pre_topc(A_1210) | ~v2_pre_topc(A_1210))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_12291])).
% 23.01/11.99  tff(c_12538, plain, (![B_1211]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1211), u1_pre_topc(B_1211))) | ~v5_pre_topc('#skF_4', '#skF_1', B_1211) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1211), u1_pre_topc(B_1211)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1211)) | ~l1_pre_topc(B_1211) | ~v2_pre_topc(B_1211) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4649, c_12520])).
% 23.01/11.99  tff(c_12556, plain, (![B_1212]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1212), u1_pre_topc(B_1212))) | ~v5_pre_topc('#skF_4', '#skF_1', B_1212) | ~l1_pre_topc(B_1212) | ~v2_pre_topc(B_1212))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_10893, c_4649, c_10893, c_12538])).
% 23.01/11.99  tff(c_12562, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11843, c_12556])).
% 23.01/11.99  tff(c_12569, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12337, c_12127, c_12324, c_12562])).
% 23.01/11.99  tff(c_12572, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_12569])).
% 23.01/11.99  tff(c_11845, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11843, c_4652])).
% 23.01/11.99  tff(c_12060, plain, (![D_1169, A_1170, B_1171]: (v5_pre_topc(D_1169, A_1170, B_1171) | ~v5_pre_topc(D_1169, g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170)), B_1171) | ~m1_subset_1(D_1169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170))), u1_struct_0(B_1171)))) | ~v1_funct_2(D_1169, u1_struct_0(g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170))), u1_struct_0(B_1171)) | ~m1_subset_1(D_1169, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1170), u1_struct_0(B_1171)))) | ~v1_funct_2(D_1169, u1_struct_0(A_1170), u1_struct_0(B_1171)) | ~v1_funct_1(D_1169) | ~l1_pre_topc(B_1171) | ~v2_pre_topc(B_1171) | ~l1_pre_topc(A_1170) | ~v2_pre_topc(A_1170))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/11.99  tff(c_12079, plain, (![A_1170, B_1171]: (v5_pre_topc('#skF_4', A_1170, B_1171) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170)), B_1171) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1170), u1_pre_topc(A_1170))), u1_struct_0(B_1171)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1170), u1_struct_0(B_1171)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1170), u1_struct_0(B_1171)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1171) | ~v2_pre_topc(B_1171) | ~l1_pre_topc(A_1170) | ~v2_pre_topc(A_1170))), inference(resolution, [status(thm)], [c_4488, c_12060])).
% 23.01/11.99  tff(c_12689, plain, (![A_1217, B_1218]: (v5_pre_topc('#skF_4', A_1217, B_1218) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1217), u1_pre_topc(A_1217)), B_1218) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1217), u1_pre_topc(A_1217))), u1_struct_0(B_1218)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1217), u1_struct_0(B_1218)) | ~l1_pre_topc(B_1218) | ~v2_pre_topc(B_1218) | ~l1_pre_topc(A_1217) | ~v2_pre_topc(A_1217))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_12079])).
% 23.01/11.99  tff(c_12707, plain, (![B_1218]: (v5_pre_topc('#skF_4', '#skF_1', B_1218) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1218) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1218)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1218)) | ~l1_pre_topc(B_1218) | ~v2_pre_topc(B_1218) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4649, c_12689])).
% 23.01/11.99  tff(c_12733, plain, (![B_1220]: (v5_pre_topc('#skF_4', '#skF_1', B_1220) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_1220) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_1220)) | ~l1_pre_topc(B_1220) | ~v2_pre_topc(B_1220))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_10893, c_4649, c_4649, c_12707])).
% 23.01/11.99  tff(c_12736, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_11843, c_12733])).
% 23.01/11.99  tff(c_12744, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12337, c_12127, c_11845, c_4806, c_12736])).
% 23.01/11.99  tff(c_12746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12572, c_12744])).
% 23.01/11.99  tff(c_12748, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_12569])).
% 23.01/11.99  tff(c_11968, plain, (![D_1153, A_1154, B_1155]: (v5_pre_topc(D_1153, A_1154, B_1155) | ~v5_pre_topc(D_1153, A_1154, g1_pre_topc(u1_struct_0(B_1155), u1_pre_topc(B_1155))) | ~m1_subset_1(D_1153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1154), u1_struct_0(g1_pre_topc(u1_struct_0(B_1155), u1_pre_topc(B_1155)))))) | ~v1_funct_2(D_1153, u1_struct_0(A_1154), u1_struct_0(g1_pre_topc(u1_struct_0(B_1155), u1_pre_topc(B_1155)))) | ~m1_subset_1(D_1153, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1154), u1_struct_0(B_1155)))) | ~v1_funct_2(D_1153, u1_struct_0(A_1154), u1_struct_0(B_1155)) | ~v1_funct_1(D_1153) | ~l1_pre_topc(B_1155) | ~v2_pre_topc(B_1155) | ~l1_pre_topc(A_1154) | ~v2_pre_topc(A_1154))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/11.99  tff(c_11987, plain, (![A_1154, B_1155]: (v5_pre_topc('#skF_4', A_1154, B_1155) | ~v5_pre_topc('#skF_4', A_1154, g1_pre_topc(u1_struct_0(B_1155), u1_pre_topc(B_1155))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1154), u1_struct_0(g1_pre_topc(u1_struct_0(B_1155), u1_pre_topc(B_1155)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1154), u1_struct_0(B_1155)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1154), u1_struct_0(B_1155)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1155) | ~v2_pre_topc(B_1155) | ~l1_pre_topc(A_1154) | ~v2_pre_topc(A_1154))), inference(resolution, [status(thm)], [c_4488, c_11968])).
% 23.01/11.99  tff(c_12751, plain, (![A_1221, B_1222]: (v5_pre_topc('#skF_4', A_1221, B_1222) | ~v5_pre_topc('#skF_4', A_1221, g1_pre_topc(u1_struct_0(B_1222), u1_pre_topc(B_1222))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1221), u1_struct_0(g1_pre_topc(u1_struct_0(B_1222), u1_pre_topc(B_1222)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1221), u1_struct_0(B_1222)) | ~l1_pre_topc(B_1222) | ~v2_pre_topc(B_1222) | ~l1_pre_topc(A_1221) | ~v2_pre_topc(A_1221))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_11987])).
% 23.01/11.99  tff(c_12769, plain, (![B_1222]: (v5_pre_topc('#skF_4', '#skF_1', B_1222) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1222), u1_pre_topc(B_1222))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1222), u1_pre_topc(B_1222)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1222)) | ~l1_pre_topc(B_1222) | ~v2_pre_topc(B_1222) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4649, c_12751])).
% 23.01/11.99  tff(c_12786, plain, (![B_1223]: (v5_pre_topc('#skF_4', '#skF_1', B_1223) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_1223), u1_pre_topc(B_1223))) | ~l1_pre_topc(B_1223) | ~v2_pre_topc(B_1223))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_10893, c_4649, c_10893, c_12769])).
% 23.01/11.99  tff(c_12789, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_12748, c_12786])).
% 23.01/11.99  tff(c_12804, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12789])).
% 23.01/11.99  tff(c_12806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4482, c_12804])).
% 23.01/11.99  tff(c_12807, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_4644])).
% 23.01/11.99  tff(c_12810, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12807, c_107])).
% 23.01/11.99  tff(c_15811, plain, (![A_1513, B_1514, C_1515]: (k1_relset_1(A_1513, B_1514, C_1515)=k1_relat_1(C_1515) | ~m1_subset_1(C_1515, k1_zfmisc_1(k2_zfmisc_1(A_1513, B_1514))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/11.99  tff(c_15826, plain, (![A_1513, B_1514]: (k1_relset_1(A_1513, B_1514, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_15811])).
% 23.01/11.99  tff(c_15903, plain, (![C_1536, A_1537, B_1538]: (v1_funct_2(C_1536, A_1537, B_1538) | k1_relset_1(A_1537, B_1538, C_1536)!=A_1537 | ~m1_subset_1(C_1536, k1_zfmisc_1(k2_zfmisc_1(A_1537, B_1538))) | ~v1_funct_1(C_1536))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/11.99  tff(c_15913, plain, (![A_1537, B_1538]: (v1_funct_2('#skF_4', A_1537, B_1538) | k1_relset_1(A_1537, B_1538, '#skF_4')!=A_1537 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_15903])).
% 23.01/11.99  tff(c_15920, plain, (![A_1537, B_1538]: (v1_funct_2('#skF_4', A_1537, B_1538) | k1_relat_1('#skF_4')!=A_1537)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_15826, c_15913])).
% 23.01/11.99  tff(c_16048, plain, (![C_1554, A_1555, B_1556]: (~v1_xboole_0(C_1554) | ~v1_funct_2(C_1554, A_1555, B_1556) | ~v1_funct_1(C_1554) | ~m1_subset_1(C_1554, k1_zfmisc_1(k2_zfmisc_1(A_1555, B_1556))) | v1_xboole_0(B_1556) | v1_xboole_0(A_1555))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/11.99  tff(c_16058, plain, (![A_1555, B_1556]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_1555, B_1556) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_1556) | v1_xboole_0(A_1555))), inference(resolution, [status(thm)], [c_4488, c_16048])).
% 23.01/11.99  tff(c_16069, plain, (![A_1557, B_1558]: (~v1_funct_2('#skF_4', A_1557, B_1558) | v1_xboole_0(B_1558) | v1_xboole_0(A_1557))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4473, c_16058])).
% 23.01/11.99  tff(c_16076, plain, (![B_1538, A_1537]: (v1_xboole_0(B_1538) | v1_xboole_0(A_1537) | k1_relat_1('#skF_4')!=A_1537)), inference(resolution, [status(thm)], [c_15920, c_16069])).
% 23.01/11.99  tff(c_16081, plain, (![A_1559]: (v1_xboole_0(A_1559) | k1_relat_1('#skF_4')!=A_1559)), inference(splitLeft, [status(thm)], [c_16076])).
% 23.01/11.99  tff(c_16148, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_16081, c_4487])).
% 23.01/11.99  tff(c_15923, plain, (![A_1539, B_1540]: (v1_funct_2('#skF_4', A_1539, B_1540) | k1_relat_1('#skF_4')!=A_1539)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_15826, c_15913])).
% 23.01/11.99  tff(c_15891, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_4480, c_4480, c_113])).
% 23.01/11.99  tff(c_15926, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_15923, c_15891])).
% 23.01/11.99  tff(c_15932, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_15926])).
% 23.01/11.99  tff(c_15934, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_15932])).
% 23.01/11.99  tff(c_16162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16148, c_15934])).
% 23.01/11.99  tff(c_16163, plain, (![B_1538]: (v1_xboole_0(B_1538))), inference(splitRight, [status(thm)], [c_16076])).
% 23.01/11.99  tff(c_13080, plain, (![A_1261, B_1262, C_1263]: (k1_relset_1(A_1261, B_1262, C_1263)=k1_relat_1(C_1263) | ~m1_subset_1(C_1263, k1_zfmisc_1(k2_zfmisc_1(A_1261, B_1262))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/11.99  tff(c_13095, plain, (![A_1261, B_1262]: (k1_relset_1(A_1261, B_1262, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_13080])).
% 23.01/11.99  tff(c_14427, plain, (![C_1397, A_1398, B_1399]: (v1_funct_2(C_1397, A_1398, B_1399) | k1_relset_1(A_1398, B_1399, C_1397)!=A_1398 | ~m1_subset_1(C_1397, k1_zfmisc_1(k2_zfmisc_1(A_1398, B_1399))) | ~v1_funct_1(C_1397))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/11.99  tff(c_14437, plain, (![A_1398, B_1399]: (v1_funct_2('#skF_4', A_1398, B_1399) | k1_relset_1(A_1398, B_1399, '#skF_4')!=A_1398 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_14427])).
% 23.01/11.99  tff(c_14444, plain, (![A_1398, B_1399]: (v1_funct_2('#skF_4', A_1398, B_1399) | k1_relat_1('#skF_4')!=A_1398)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_13095, c_14437])).
% 23.01/11.99  tff(c_14599, plain, (![C_1415, A_1416, B_1417]: (~v1_xboole_0(C_1415) | ~v1_funct_2(C_1415, A_1416, B_1417) | ~v1_funct_1(C_1415) | ~m1_subset_1(C_1415, k1_zfmisc_1(k2_zfmisc_1(A_1416, B_1417))) | v1_xboole_0(B_1417) | v1_xboole_0(A_1416))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/11.99  tff(c_14609, plain, (![A_1416, B_1417]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_1416, B_1417) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_1417) | v1_xboole_0(A_1416))), inference(resolution, [status(thm)], [c_4488, c_14599])).
% 23.01/11.99  tff(c_14620, plain, (![A_1418, B_1419]: (~v1_funct_2('#skF_4', A_1418, B_1419) | v1_xboole_0(B_1419) | v1_xboole_0(A_1418))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4473, c_14609])).
% 23.01/11.99  tff(c_14627, plain, (![B_1399, A_1398]: (v1_xboole_0(B_1399) | v1_xboole_0(A_1398) | k1_relat_1('#skF_4')!=A_1398)), inference(resolution, [status(thm)], [c_14444, c_14620])).
% 23.01/11.99  tff(c_14632, plain, (![A_1420]: (v1_xboole_0(A_1420) | k1_relat_1('#skF_4')!=A_1420)), inference(splitLeft, [status(thm)], [c_14627])).
% 23.01/11.99  tff(c_14676, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_14632, c_4487])).
% 23.01/11.99  tff(c_14447, plain, (![A_1400, B_1401]: (v1_funct_2('#skF_4', A_1400, B_1401) | k1_relat_1('#skF_4')!=A_1400)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_13095, c_14437])).
% 23.01/11.99  tff(c_13163, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_4480, c_4480, c_113])).
% 23.01/11.99  tff(c_14453, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_14447, c_13163])).
% 23.01/11.99  tff(c_14457, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_14453])).
% 23.01/11.99  tff(c_14458, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_14457])).
% 23.01/11.99  tff(c_14690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14676, c_14458])).
% 23.01/11.99  tff(c_14691, plain, (![B_1399]: (v1_xboole_0(B_1399))), inference(splitRight, [status(thm)], [c_14627])).
% 23.01/11.99  tff(c_12847, plain, (![A_1230]: (m1_subset_1(u1_pre_topc(A_1230), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1230)))) | ~l1_pre_topc(A_1230))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/11.99  tff(c_12862, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12807, c_12847])).
% 23.01/11.99  tff(c_12868, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_12862])).
% 23.01/11.99  tff(c_12987, plain, (![A_1247, C_1248, B_1249]: (m1_subset_1(A_1247, C_1248) | ~m1_subset_1(B_1249, k1_zfmisc_1(C_1248)) | ~r2_hidden(A_1247, B_1249))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.01/11.99  tff(c_13007, plain, (![A_1252]: (m1_subset_1(A_1252, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_1252, u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_12868, c_12987])).
% 23.01/11.99  tff(c_13012, plain, (![B_6]: (m1_subset_1(B_6, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_6, u1_pre_topc('#skF_2')) | v1_xboole_0(u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_14, c_13007])).
% 23.01/11.99  tff(c_13034, plain, (v1_xboole_0(u1_pre_topc('#skF_2'))), inference(splitLeft, [status(thm)], [c_13012])).
% 23.01/11.99  tff(c_13040, plain, (u1_pre_topc('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_13034, c_4487])).
% 23.01/11.99  tff(c_12811, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_12807, c_82])).
% 23.01/11.99  tff(c_13049, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_13040, c_12811])).
% 23.01/11.99  tff(c_13185, plain, (![C_1287, A_1288, B_1289]: (v1_partfun1(C_1287, A_1288) | ~v1_funct_2(C_1287, A_1288, B_1289) | ~v1_funct_1(C_1287) | ~m1_subset_1(C_1287, k1_zfmisc_1(k2_zfmisc_1(A_1288, B_1289))) | v1_xboole_0(B_1289))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/11.99  tff(c_13195, plain, (![A_1288, B_1289]: (v1_partfun1('#skF_4', A_1288) | ~v1_funct_2('#skF_4', A_1288, B_1289) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_1289))), inference(resolution, [status(thm)], [c_4488, c_13185])).
% 23.01/11.99  tff(c_13205, plain, (![A_1290, B_1291]: (v1_partfun1('#skF_4', A_1290) | ~v1_funct_2('#skF_4', A_1290, B_1291) | v1_xboole_0(B_1291))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_13195])).
% 23.01/11.99  tff(c_13212, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_13049, c_13205])).
% 23.01/11.99  tff(c_13215, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_13212])).
% 23.01/11.99  tff(c_13221, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_13215, c_4487])).
% 23.01/11.99  tff(c_13224, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13221, c_13049])).
% 23.01/11.99  tff(c_12934, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12807, c_243])).
% 23.01/11.99  tff(c_13045, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13040, c_12934])).
% 23.01/11.99  tff(c_12941, plain, (![A_1241]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_1241), u1_pre_topc(A_1241))) | ~l1_pre_topc(A_1241) | ~v2_pre_topc(A_1241))), inference(cnfTransformation, [status(thm)], [f_178])).
% 23.01/11.99  tff(c_12944, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12807, c_12941])).
% 23.01/11.99  tff(c_12946, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12944])).
% 23.01/11.99  tff(c_13044, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13040, c_12946])).
% 23.01/11.99  tff(c_12818, plain, (![A_1224, B_1225]: (l1_pre_topc(g1_pre_topc(A_1224, B_1225)) | ~m1_subset_1(B_1225, k1_zfmisc_1(k1_zfmisc_1(A_1224))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/11.99  tff(c_12827, plain, (![A_1224]: (l1_pre_topc(g1_pre_topc(A_1224, '#skF_4')))), inference(resolution, [status(thm)], [c_4488, c_12818])).
% 23.01/11.99  tff(c_4490, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_4480, c_8])).
% 23.01/11.99  tff(c_13825, plain, (![D_1335, A_1336, B_1337]: (v5_pre_topc(D_1335, A_1336, B_1337) | ~v5_pre_topc(D_1335, g1_pre_topc(u1_struct_0(A_1336), u1_pre_topc(A_1336)), B_1337) | ~m1_subset_1(D_1335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1336), u1_pre_topc(A_1336))), u1_struct_0(B_1337)))) | ~v1_funct_2(D_1335, u1_struct_0(g1_pre_topc(u1_struct_0(A_1336), u1_pre_topc(A_1336))), u1_struct_0(B_1337)) | ~m1_subset_1(D_1335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1336), u1_struct_0(B_1337)))) | ~v1_funct_2(D_1335, u1_struct_0(A_1336), u1_struct_0(B_1337)) | ~v1_funct_1(D_1335) | ~l1_pre_topc(B_1337) | ~v2_pre_topc(B_1337) | ~l1_pre_topc(A_1336) | ~v2_pre_topc(A_1336))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/11.99  tff(c_13831, plain, (![D_1335, A_1336]: (v5_pre_topc(D_1335, A_1336, g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_1335, g1_pre_topc(u1_struct_0(A_1336), u1_pre_topc(A_1336)), g1_pre_topc('#skF_4', '#skF_4')) | ~m1_subset_1(D_1335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1336), u1_pre_topc(A_1336))), '#skF_4'))) | ~v1_funct_2(D_1335, u1_struct_0(g1_pre_topc(u1_struct_0(A_1336), u1_pre_topc(A_1336))), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | ~m1_subset_1(D_1335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1336), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))))) | ~v1_funct_2(D_1335, u1_struct_0(A_1336), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | ~v1_funct_1(D_1335) | ~l1_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~l1_pre_topc(A_1336) | ~v2_pre_topc(A_1336))), inference(superposition, [status(thm), theory('equality')], [c_13221, c_13825])).
% 23.01/11.99  tff(c_13978, plain, (![D_1357, A_1358]: (v5_pre_topc(D_1357, A_1358, g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_1357, g1_pre_topc(u1_struct_0(A_1358), u1_pre_topc(A_1358)), g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2(D_1357, u1_struct_0(g1_pre_topc(u1_struct_0(A_1358), u1_pre_topc(A_1358))), '#skF_4') | ~m1_subset_1(D_1357, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_1357, u1_struct_0(A_1358), '#skF_4') | ~v1_funct_1(D_1357) | ~l1_pre_topc(A_1358) | ~v2_pre_topc(A_1358))), inference(demodulation, [status(thm), theory('equality')], [c_13044, c_12827, c_13221, c_4490, c_13221, c_13221, c_4490, c_13831])).
% 23.01/11.99  tff(c_13984, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_13045, c_13978])).
% 23.01/11.99  tff(c_13995, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_12810, c_4488, c_13224, c_13984])).
% 23.01/11.99  tff(c_13938, plain, (![D_1350, A_1351, B_1352]: (v5_pre_topc(D_1350, A_1351, B_1352) | ~v5_pre_topc(D_1350, A_1351, g1_pre_topc(u1_struct_0(B_1352), u1_pre_topc(B_1352))) | ~m1_subset_1(D_1350, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1351), u1_struct_0(g1_pre_topc(u1_struct_0(B_1352), u1_pre_topc(B_1352)))))) | ~v1_funct_2(D_1350, u1_struct_0(A_1351), u1_struct_0(g1_pre_topc(u1_struct_0(B_1352), u1_pre_topc(B_1352)))) | ~m1_subset_1(D_1350, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1351), u1_struct_0(B_1352)))) | ~v1_funct_2(D_1350, u1_struct_0(A_1351), u1_struct_0(B_1352)) | ~v1_funct_1(D_1350) | ~l1_pre_topc(B_1352) | ~v2_pre_topc(B_1352) | ~l1_pre_topc(A_1351) | ~v2_pre_topc(A_1351))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/11.99  tff(c_13957, plain, (![A_1351, B_1352]: (v5_pre_topc('#skF_4', A_1351, B_1352) | ~v5_pre_topc('#skF_4', A_1351, g1_pre_topc(u1_struct_0(B_1352), u1_pre_topc(B_1352))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1351), u1_struct_0(g1_pre_topc(u1_struct_0(B_1352), u1_pre_topc(B_1352)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1351), u1_struct_0(B_1352)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1351), u1_struct_0(B_1352)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1352) | ~v2_pre_topc(B_1352) | ~l1_pre_topc(A_1351) | ~v2_pre_topc(A_1351))), inference(resolution, [status(thm)], [c_4488, c_13938])).
% 23.01/11.99  tff(c_14334, plain, (![A_1392, B_1393]: (v5_pre_topc('#skF_4', A_1392, B_1393) | ~v5_pre_topc('#skF_4', A_1392, g1_pre_topc(u1_struct_0(B_1393), u1_pre_topc(B_1393))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1392), u1_struct_0(g1_pre_topc(u1_struct_0(B_1393), u1_pre_topc(B_1393)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1392), u1_struct_0(B_1393)) | ~l1_pre_topc(B_1393) | ~v2_pre_topc(B_1393) | ~l1_pre_topc(A_1392) | ~v2_pre_topc(A_1392))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_13957])).
% 23.01/11.99  tff(c_14349, plain, (![A_1392]: (v5_pre_topc('#skF_4', A_1392, '#skF_2') | ~v5_pre_topc('#skF_4', A_1392, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1392), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), '#skF_4'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1392), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1392) | ~v2_pre_topc(A_1392))), inference(superposition, [status(thm), theory('equality')], [c_13040, c_14334])).
% 23.01/11.99  tff(c_14413, plain, (![A_1396]: (v5_pre_topc('#skF_4', A_1396, '#skF_2') | ~v5_pre_topc('#skF_4', A_1396, g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(A_1396), '#skF_4') | ~l1_pre_topc(A_1396) | ~v2_pre_topc(A_1396))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12807, c_13221, c_12807, c_12807, c_13040, c_14349])).
% 23.01/11.99  tff(c_14416, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_13995, c_14413])).
% 23.01/11.99  tff(c_14422, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_12810, c_14416])).
% 23.01/11.99  tff(c_14424, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4482, c_14422])).
% 23.01/11.99  tff(c_14426, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_13212])).
% 23.01/11.99  tff(c_14739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14691, c_14426])).
% 23.01/11.99  tff(c_14741, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_14457])).
% 23.01/11.99  tff(c_14799, plain, (![B_1399]: (v1_funct_2('#skF_4', '#skF_4', B_1399))), inference(demodulation, [status(thm), theory('equality')], [c_14741, c_14444])).
% 23.01/11.99  tff(c_14425, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_13212])).
% 23.01/11.99  tff(c_12830, plain, (![C_1227, A_1228, B_1229]: (v4_relat_1(C_1227, A_1228) | ~m1_subset_1(C_1227, k1_zfmisc_1(k2_zfmisc_1(A_1228, B_1229))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/11.99  tff(c_12845, plain, (![A_1228]: (v4_relat_1('#skF_4', A_1228))), inference(resolution, [status(thm)], [c_4488, c_12830])).
% 23.01/11.99  tff(c_13015, plain, (![B_1257, A_1258]: (k1_relat_1(B_1257)=A_1258 | ~v1_partfun1(B_1257, A_1258) | ~v4_relat_1(B_1257, A_1258) | ~v1_relat_1(B_1257))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/11.99  tff(c_13018, plain, (![A_1228]: (k1_relat_1('#skF_4')=A_1228 | ~v1_partfun1('#skF_4', A_1228) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_12845, c_13015])).
% 23.01/11.99  tff(c_13021, plain, (![A_1228]: (k1_relat_1('#skF_4')=A_1228 | ~v1_partfun1('#skF_4', A_1228))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_13018])).
% 23.01/11.99  tff(c_14748, plain, (![A_1228]: (A_1228='#skF_4' | ~v1_partfun1('#skF_4', A_1228))), inference(demodulation, [status(thm), theory('equality')], [c_14741, c_13021])).
% 23.01/11.99  tff(c_14798, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_14425, c_14748])).
% 23.01/11.99  tff(c_15151, plain, (![D_1472, A_1473, B_1474]: (v5_pre_topc(D_1472, A_1473, B_1474) | ~v5_pre_topc(D_1472, g1_pre_topc(u1_struct_0(A_1473), u1_pre_topc(A_1473)), B_1474) | ~m1_subset_1(D_1472, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1473), u1_pre_topc(A_1473))), u1_struct_0(B_1474)))) | ~v1_funct_2(D_1472, u1_struct_0(g1_pre_topc(u1_struct_0(A_1473), u1_pre_topc(A_1473))), u1_struct_0(B_1474)) | ~m1_subset_1(D_1472, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1473), u1_struct_0(B_1474)))) | ~v1_funct_2(D_1472, u1_struct_0(A_1473), u1_struct_0(B_1474)) | ~v1_funct_1(D_1472) | ~l1_pre_topc(B_1474) | ~v2_pre_topc(B_1474) | ~l1_pre_topc(A_1473) | ~v2_pre_topc(A_1473))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/11.99  tff(c_15173, plain, (![A_1473, B_1474]: (v5_pre_topc('#skF_4', A_1473, B_1474) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1473), u1_pre_topc(A_1473)), B_1474) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1473), u1_pre_topc(A_1473))), u1_struct_0(B_1474)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1473), u1_struct_0(B_1474)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1473), u1_struct_0(B_1474)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1474) | ~v2_pre_topc(B_1474) | ~l1_pre_topc(A_1473) | ~v2_pre_topc(A_1473))), inference(resolution, [status(thm)], [c_4488, c_15151])).
% 23.01/11.99  tff(c_15463, plain, (![A_1490, B_1491]: (v5_pre_topc('#skF_4', A_1490, B_1491) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1490), u1_pre_topc(A_1490)), B_1491) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1490), u1_pre_topc(A_1490))), u1_struct_0(B_1491)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1490), u1_struct_0(B_1491)) | ~l1_pre_topc(B_1491) | ~v2_pre_topc(B_1491) | ~l1_pre_topc(A_1490) | ~v2_pre_topc(A_1490))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_15173])).
% 23.01/11.99  tff(c_15487, plain, (![A_1490]: (v5_pre_topc('#skF_4', A_1490, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1490), u1_pre_topc(A_1490)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1490), u1_pre_topc(A_1490))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1490), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1490) | ~v2_pre_topc(A_1490))), inference(superposition, [status(thm), theory('equality')], [c_12807, c_15463])).
% 23.01/11.99  tff(c_15595, plain, (![A_1498]: (v5_pre_topc('#skF_4', A_1498, '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1498), u1_pre_topc(A_1498)), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1498), u1_pre_topc(A_1498))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1498), '#skF_4') | ~l1_pre_topc(A_1498) | ~v2_pre_topc(A_1498))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12807, c_15487])).
% 23.01/11.99  tff(c_15604, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14798, c_15595])).
% 23.01/11.99  tff(c_15619, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_12810, c_14799, c_15604])).
% 23.01/11.99  tff(c_15620, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_4482, c_15619])).
% 23.01/11.99  tff(c_12863, plain, (![A_1230]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1230), u1_pre_topc(A_1230))) | ~l1_pre_topc(A_1230))), inference(resolution, [status(thm)], [c_12847, c_60])).
% 23.01/11.99  tff(c_12864, plain, (![A_1230]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_1230), u1_pre_topc(A_1230))) | ~l1_pre_topc(A_1230))), inference(resolution, [status(thm)], [c_12847, c_62])).
% 23.01/11.99  tff(c_14840, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14798, c_12864])).
% 23.01/11.99  tff(c_15020, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_14840])).
% 23.01/11.99  tff(c_15023, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12863, c_15020])).
% 23.01/11.99  tff(c_15027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_15023])).
% 23.01/11.99  tff(c_15029, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_14840])).
% 23.01/11.99  tff(c_14846, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14798, c_64])).
% 23.01/11.99  tff(c_15195, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_15029, c_14846])).
% 23.01/11.99  tff(c_15217, plain, (![A_1475]: (m1_subset_1(A_1475, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_1475, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(resolution, [status(thm)], [c_15195, c_24])).
% 23.01/12.00  tff(c_15222, plain, (![B_6]: (m1_subset_1(B_6, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_6, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(resolution, [status(thm)], [c_14, c_15217])).
% 23.01/12.00  tff(c_15253, plain, (v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_15222])).
% 23.01/12.00  tff(c_15265, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_15253, c_4487])).
% 23.01/12.00  tff(c_15042, plain, (![D_1452, A_1453, B_1454]: (v5_pre_topc(D_1452, A_1453, g1_pre_topc(u1_struct_0(B_1454), u1_pre_topc(B_1454))) | ~v5_pre_topc(D_1452, A_1453, B_1454) | ~m1_subset_1(D_1452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1453), u1_struct_0(g1_pre_topc(u1_struct_0(B_1454), u1_pre_topc(B_1454)))))) | ~v1_funct_2(D_1452, u1_struct_0(A_1453), u1_struct_0(g1_pre_topc(u1_struct_0(B_1454), u1_pre_topc(B_1454)))) | ~m1_subset_1(D_1452, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1453), u1_struct_0(B_1454)))) | ~v1_funct_2(D_1452, u1_struct_0(A_1453), u1_struct_0(B_1454)) | ~v1_funct_1(D_1452) | ~l1_pre_topc(B_1454) | ~v2_pre_topc(B_1454) | ~l1_pre_topc(A_1453) | ~v2_pre_topc(A_1453))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_15064, plain, (![A_1453, B_1454]: (v5_pre_topc('#skF_4', A_1453, g1_pre_topc(u1_struct_0(B_1454), u1_pre_topc(B_1454))) | ~v5_pre_topc('#skF_4', A_1453, B_1454) | ~v1_funct_2('#skF_4', u1_struct_0(A_1453), u1_struct_0(g1_pre_topc(u1_struct_0(B_1454), u1_pre_topc(B_1454)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1453), u1_struct_0(B_1454)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1453), u1_struct_0(B_1454)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1454) | ~v2_pre_topc(B_1454) | ~l1_pre_topc(A_1453) | ~v2_pre_topc(A_1453))), inference(resolution, [status(thm)], [c_4488, c_15042])).
% 23.01/12.00  tff(c_15626, plain, (![A_1499, B_1500]: (v5_pre_topc('#skF_4', A_1499, g1_pre_topc(u1_struct_0(B_1500), u1_pre_topc(B_1500))) | ~v5_pre_topc('#skF_4', A_1499, B_1500) | ~v1_funct_2('#skF_4', u1_struct_0(A_1499), u1_struct_0(g1_pre_topc(u1_struct_0(B_1500), u1_pre_topc(B_1500)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1499), u1_struct_0(B_1500)) | ~l1_pre_topc(B_1500) | ~v2_pre_topc(B_1500) | ~l1_pre_topc(A_1499) | ~v2_pre_topc(A_1499))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_15064])).
% 23.01/12.00  tff(c_15647, plain, (![B_1500]: (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0(B_1500), u1_pre_topc(B_1500))) | ~v5_pre_topc('#skF_4', '#skF_2', B_1500) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1500), u1_pre_topc(B_1500)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_1500)) | ~l1_pre_topc(B_1500) | ~v2_pre_topc(B_1500) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12807, c_15626])).
% 23.01/12.00  tff(c_15672, plain, (![B_1501]: (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0(B_1501), u1_pre_topc(B_1501))) | ~v5_pre_topc('#skF_4', '#skF_2', B_1501) | ~l1_pre_topc(B_1501) | ~v2_pre_topc(B_1501))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_14799, c_12807, c_14799, c_15647])).
% 23.01/12.00  tff(c_15678, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_14798, c_15672])).
% 23.01/12.00  tff(c_15688, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_15029, c_15265, c_15678])).
% 23.01/12.00  tff(c_15694, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_15688])).
% 23.01/12.00  tff(c_15697, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_15694])).
% 23.01/12.00  tff(c_15701, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_15697])).
% 23.01/12.00  tff(c_15703, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_15688])).
% 23.01/12.00  tff(c_15345, plain, (![D_1481, A_1482, B_1483]: (v5_pre_topc(D_1481, A_1482, B_1483) | ~v5_pre_topc(D_1481, A_1482, g1_pre_topc(u1_struct_0(B_1483), u1_pre_topc(B_1483))) | ~m1_subset_1(D_1481, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1482), u1_struct_0(g1_pre_topc(u1_struct_0(B_1483), u1_pre_topc(B_1483)))))) | ~v1_funct_2(D_1481, u1_struct_0(A_1482), u1_struct_0(g1_pre_topc(u1_struct_0(B_1483), u1_pre_topc(B_1483)))) | ~m1_subset_1(D_1481, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1482), u1_struct_0(B_1483)))) | ~v1_funct_2(D_1481, u1_struct_0(A_1482), u1_struct_0(B_1483)) | ~v1_funct_1(D_1481) | ~l1_pre_topc(B_1483) | ~v2_pre_topc(B_1483) | ~l1_pre_topc(A_1482) | ~v2_pre_topc(A_1482))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_15370, plain, (![A_1482, B_1483]: (v5_pre_topc('#skF_4', A_1482, B_1483) | ~v5_pre_topc('#skF_4', A_1482, g1_pre_topc(u1_struct_0(B_1483), u1_pre_topc(B_1483))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1482), u1_struct_0(g1_pre_topc(u1_struct_0(B_1483), u1_pre_topc(B_1483)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1482), u1_struct_0(B_1483)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1482), u1_struct_0(B_1483)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1483) | ~v2_pre_topc(B_1483) | ~l1_pre_topc(A_1482) | ~v2_pre_topc(A_1482))), inference(resolution, [status(thm)], [c_4488, c_15345])).
% 23.01/12.00  tff(c_15704, plain, (![A_1502, B_1503]: (v5_pre_topc('#skF_4', A_1502, B_1503) | ~v5_pre_topc('#skF_4', A_1502, g1_pre_topc(u1_struct_0(B_1503), u1_pre_topc(B_1503))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1502), u1_struct_0(g1_pre_topc(u1_struct_0(B_1503), u1_pre_topc(B_1503)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1502), u1_struct_0(B_1503)) | ~l1_pre_topc(B_1503) | ~v2_pre_topc(B_1503) | ~l1_pre_topc(A_1502) | ~v2_pre_topc(A_1502))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_15370])).
% 23.01/12.00  tff(c_15710, plain, (![B_1503]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1503) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_1503), u1_pre_topc(B_1503))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_1503), u1_pre_topc(B_1503)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_1503)) | ~l1_pre_topc(B_1503) | ~v2_pre_topc(B_1503) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_14798, c_15704])).
% 23.01/12.00  tff(c_15751, plain, (![B_1504]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1504) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_1504), u1_pre_topc(B_1504))) | ~l1_pre_topc(B_1504) | ~v2_pre_topc(B_1504))), inference(demodulation, [status(thm), theory('equality')], [c_15703, c_15029, c_14799, c_14798, c_14799, c_15710])).
% 23.01/12.00  tff(c_15763, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_13040, c_15751])).
% 23.01/12.00  tff(c_15773, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_13045, c_12807, c_15763])).
% 23.01/12.00  tff(c_15775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15620, c_15773])).
% 23.01/12.00  tff(c_15777, plain, (~v1_xboole_0(u1_pre_topc('#skF_2'))), inference(splitRight, [status(thm)], [c_13012])).
% 23.01/12.00  tff(c_16210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16163, c_15777])).
% 23.01/12.00  tff(c_16212, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_15932])).
% 23.01/12.00  tff(c_16237, plain, (![A_1537, B_1538]: (v1_funct_2('#skF_4', A_1537, B_1538) | A_1537!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16212, c_15920])).
% 23.01/12.00  tff(c_16287, plain, (![C_1569, A_1570, B_1571]: (~v1_xboole_0(C_1569) | ~v1_funct_2(C_1569, A_1570, B_1571) | ~v1_funct_1(C_1569) | ~m1_subset_1(C_1569, k1_zfmisc_1(k2_zfmisc_1(A_1570, B_1571))) | v1_xboole_0(B_1571) | v1_xboole_0(A_1570))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_16297, plain, (![A_1570, B_1571]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_1570, B_1571) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_1571) | v1_xboole_0(A_1570))), inference(resolution, [status(thm)], [c_4488, c_16287])).
% 23.01/12.00  tff(c_16308, plain, (![A_1572, B_1573]: (~v1_funct_2('#skF_4', A_1572, B_1573) | v1_xboole_0(B_1573) | v1_xboole_0(A_1572))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4473, c_16297])).
% 23.01/12.00  tff(c_16318, plain, (![B_1538, A_1537]: (v1_xboole_0(B_1538) | v1_xboole_0(A_1537) | A_1537!='#skF_4')), inference(resolution, [status(thm)], [c_16237, c_16308])).
% 23.01/12.00  tff(c_16322, plain, (![A_1537]: (v1_xboole_0(A_1537) | A_1537!='#skF_4')), inference(splitLeft, [status(thm)], [c_16318])).
% 23.01/12.00  tff(c_16321, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_12811, c_16308])).
% 23.01/12.00  tff(c_16369, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_16321])).
% 23.01/12.00  tff(c_16416, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_16369, c_4487])).
% 23.01/12.00  tff(c_16451, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16416, c_12863])).
% 23.01/12.00  tff(c_16550, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_16451])).
% 23.01/12.00  tff(c_16556, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12863, c_16550])).
% 23.01/12.00  tff(c_16561, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_16556])).
% 23.01/12.00  tff(c_16563, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_16451])).
% 23.01/12.00  tff(c_16454, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16416, c_64])).
% 23.01/12.00  tff(c_16650, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16563, c_16454])).
% 23.01/12.00  tff(c_16672, plain, (![A_1612]: (m1_subset_1(A_1612, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_1612, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(resolution, [status(thm)], [c_16650, c_24])).
% 23.01/12.00  tff(c_16677, plain, (![B_6]: (m1_subset_1(B_6, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_6, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))), inference(resolution, [status(thm)], [c_14, c_16672])).
% 23.01/12.00  tff(c_16760, plain, (v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_16677])).
% 23.01/12.00  tff(c_16772, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_16760, c_4487])).
% 23.01/12.00  tff(c_16442, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16416, c_66])).
% 23.01/12.00  tff(c_16907, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16563, c_16772, c_16442])).
% 23.01/12.00  tff(c_16908, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_16907])).
% 23.01/12.00  tff(c_16911, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_16908])).
% 23.01/12.00  tff(c_16915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_16911])).
% 23.01/12.00  tff(c_16917, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_16907])).
% 23.01/12.00  tff(c_16818, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16772, c_66])).
% 23.01/12.00  tff(c_16853, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_16563, c_16416, c_16818])).
% 23.01/12.00  tff(c_16905, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_16853])).
% 23.01/12.00  tff(c_16919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16917, c_16905])).
% 23.01/12.00  tff(c_16921, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_16853])).
% 23.01/12.00  tff(c_16266, plain, (![B_1538]: (v1_funct_2('#skF_4', '#skF_4', B_1538))), inference(demodulation, [status(thm), theory('equality')], [c_16212, c_15920])).
% 23.01/12.00  tff(c_16576, plain, (![D_1600, A_1601, B_1602]: (v5_pre_topc(D_1600, A_1601, B_1602) | ~v5_pre_topc(D_1600, A_1601, g1_pre_topc(u1_struct_0(B_1602), u1_pre_topc(B_1602))) | ~m1_subset_1(D_1600, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1601), u1_struct_0(g1_pre_topc(u1_struct_0(B_1602), u1_pre_topc(B_1602)))))) | ~v1_funct_2(D_1600, u1_struct_0(A_1601), u1_struct_0(g1_pre_topc(u1_struct_0(B_1602), u1_pre_topc(B_1602)))) | ~m1_subset_1(D_1600, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1601), u1_struct_0(B_1602)))) | ~v1_funct_2(D_1600, u1_struct_0(A_1601), u1_struct_0(B_1602)) | ~v1_funct_1(D_1600) | ~l1_pre_topc(B_1602) | ~v2_pre_topc(B_1602) | ~l1_pre_topc(A_1601) | ~v2_pre_topc(A_1601))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_16595, plain, (![A_1601, B_1602]: (v5_pre_topc('#skF_4', A_1601, B_1602) | ~v5_pre_topc('#skF_4', A_1601, g1_pre_topc(u1_struct_0(B_1602), u1_pre_topc(B_1602))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1601), u1_struct_0(g1_pre_topc(u1_struct_0(B_1602), u1_pre_topc(B_1602)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1601), u1_struct_0(B_1602)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1601), u1_struct_0(B_1602)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1602) | ~v2_pre_topc(B_1602) | ~l1_pre_topc(A_1601) | ~v2_pre_topc(A_1601))), inference(resolution, [status(thm)], [c_4488, c_16576])).
% 23.01/12.00  tff(c_16868, plain, (![A_1625, B_1626]: (v5_pre_topc('#skF_4', A_1625, B_1626) | ~v5_pre_topc('#skF_4', A_1625, g1_pre_topc(u1_struct_0(B_1626), u1_pre_topc(B_1626))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1625), u1_struct_0(g1_pre_topc(u1_struct_0(B_1626), u1_pre_topc(B_1626)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1625), u1_struct_0(B_1626)) | ~l1_pre_topc(B_1626) | ~v2_pre_topc(B_1626) | ~l1_pre_topc(A_1625) | ~v2_pre_topc(A_1625))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_16595])).
% 23.01/12.00  tff(c_16889, plain, (![A_1625]: (v5_pre_topc('#skF_4', A_1625, '#skF_2') | ~v5_pre_topc('#skF_4', A_1625, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1625), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1625), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1625) | ~v2_pre_topc(A_1625))), inference(superposition, [status(thm), theory('equality')], [c_12807, c_16868])).
% 23.01/12.00  tff(c_17218, plain, (![A_1649]: (v5_pre_topc('#skF_4', A_1649, '#skF_2') | ~v5_pre_topc('#skF_4', A_1649, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1649), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1649), '#skF_4') | ~l1_pre_topc(A_1649) | ~v2_pre_topc(A_1649))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12807, c_12807, c_16889])).
% 23.01/12.00  tff(c_17221, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_16416, c_17218])).
% 23.01/12.00  tff(c_17229, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16921, c_16563, c_16266, c_16416, c_16266, c_12934, c_17221])).
% 23.01/12.00  tff(c_16502, plain, (![D_1588, A_1589, B_1590]: (v5_pre_topc(D_1588, A_1589, B_1590) | ~v5_pre_topc(D_1588, g1_pre_topc(u1_struct_0(A_1589), u1_pre_topc(A_1589)), B_1590) | ~m1_subset_1(D_1588, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1589), u1_pre_topc(A_1589))), u1_struct_0(B_1590)))) | ~v1_funct_2(D_1588, u1_struct_0(g1_pre_topc(u1_struct_0(A_1589), u1_pre_topc(A_1589))), u1_struct_0(B_1590)) | ~m1_subset_1(D_1588, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1589), u1_struct_0(B_1590)))) | ~v1_funct_2(D_1588, u1_struct_0(A_1589), u1_struct_0(B_1590)) | ~v1_funct_1(D_1588) | ~l1_pre_topc(B_1590) | ~v2_pre_topc(B_1590) | ~l1_pre_topc(A_1589) | ~v2_pre_topc(A_1589))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_16521, plain, (![A_1589, B_1590]: (v5_pre_topc('#skF_4', A_1589, B_1590) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1589), u1_pre_topc(A_1589)), B_1590) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1589), u1_pre_topc(A_1589))), u1_struct_0(B_1590)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1589), u1_struct_0(B_1590)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1589), u1_struct_0(B_1590)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1590) | ~v2_pre_topc(B_1590) | ~l1_pre_topc(A_1589) | ~v2_pre_topc(A_1589))), inference(resolution, [status(thm)], [c_4488, c_16502])).
% 23.01/12.00  tff(c_17076, plain, (![A_1637, B_1638]: (v5_pre_topc('#skF_4', A_1637, B_1638) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1637), u1_pre_topc(A_1637)), B_1638) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1637), u1_pre_topc(A_1637))), u1_struct_0(B_1638)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1637), u1_struct_0(B_1638)) | ~l1_pre_topc(B_1638) | ~v2_pre_topc(B_1638) | ~l1_pre_topc(A_1637) | ~v2_pre_topc(A_1637))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_16521])).
% 23.01/12.00  tff(c_17085, plain, (![B_1638]: (v5_pre_topc('#skF_4', '#skF_1', B_1638) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1638) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_1638)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1638)) | ~l1_pre_topc(B_1638) | ~v2_pre_topc(B_1638) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16416, c_17076])).
% 23.01/12.00  tff(c_17103, plain, (![B_1638]: (v5_pre_topc('#skF_4', '#skF_1', B_1638) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_1638) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_1638)) | ~l1_pre_topc(B_1638) | ~v2_pre_topc(B_1638))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_16266, c_17085])).
% 23.01/12.00  tff(c_17239, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_17229, c_17103])).
% 23.01/12.00  tff(c_17245, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12810, c_12807, c_17239])).
% 23.01/12.00  tff(c_17247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4482, c_17245])).
% 23.01/12.00  tff(c_17249, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_16321])).
% 23.01/12.00  tff(c_17356, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))!='#skF_4'), inference(resolution, [status(thm)], [c_16322, c_17249])).
% 23.01/12.00  tff(c_15856, plain, (![B_1522, C_1523, A_1524]: (B_1522='#skF_4' | v1_partfun1(C_1523, A_1524) | ~v1_funct_2(C_1523, A_1524, B_1522) | ~m1_subset_1(C_1523, k1_zfmisc_1(k2_zfmisc_1(A_1524, B_1522))) | ~v1_funct_1(C_1523))), inference(demodulation, [status(thm), theory('equality')], [c_4480, c_58])).
% 23.01/12.00  tff(c_15866, plain, (![B_1522, A_1524]: (B_1522='#skF_4' | v1_partfun1('#skF_4', A_1524) | ~v1_funct_2('#skF_4', A_1524, B_1522) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4488, c_15856])).
% 23.01/12.00  tff(c_15876, plain, (![B_1525, A_1526]: (B_1525='#skF_4' | v1_partfun1('#skF_4', A_1526) | ~v1_funct_2('#skF_4', A_1526, B_1525))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_15866])).
% 23.01/12.00  tff(c_15885, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_12811, c_15876])).
% 23.01/12.00  tff(c_16258, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_15885])).
% 23.01/12.00  tff(c_16239, plain, (![A_1228]: (A_1228='#skF_4' | ~v1_partfun1('#skF_4', A_1228))), inference(demodulation, [status(thm), theory('equality')], [c_16212, c_13021])).
% 23.01/12.00  tff(c_17359, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_16258, c_16239])).
% 23.01/12.00  tff(c_17363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17356, c_17359])).
% 23.01/12.00  tff(c_17364, plain, (![B_1538]: (v1_xboole_0(B_1538))), inference(splitRight, [status(thm)], [c_16318])).
% 23.01/12.00  tff(c_17410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17364, c_15777])).
% 23.01/12.00  tff(c_17411, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_15885])).
% 23.01/12.00  tff(c_17431, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17411, c_12811])).
% 23.01/12.00  tff(c_12882, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_12868, c_60])).
% 23.01/12.00  tff(c_17841, plain, (![D_1712, A_1713, B_1714]: (v5_pre_topc(D_1712, A_1713, B_1714) | ~v5_pre_topc(D_1712, g1_pre_topc(u1_struct_0(A_1713), u1_pre_topc(A_1713)), B_1714) | ~m1_subset_1(D_1712, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1713), u1_pre_topc(A_1713))), u1_struct_0(B_1714)))) | ~v1_funct_2(D_1712, u1_struct_0(g1_pre_topc(u1_struct_0(A_1713), u1_pre_topc(A_1713))), u1_struct_0(B_1714)) | ~m1_subset_1(D_1712, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1713), u1_struct_0(B_1714)))) | ~v1_funct_2(D_1712, u1_struct_0(A_1713), u1_struct_0(B_1714)) | ~v1_funct_1(D_1712) | ~l1_pre_topc(B_1714) | ~v2_pre_topc(B_1714) | ~l1_pre_topc(A_1713) | ~v2_pre_topc(A_1713))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_17847, plain, (![D_1712, A_1713]: (v5_pre_topc(D_1712, A_1713, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1712, g1_pre_topc(u1_struct_0(A_1713), u1_pre_topc(A_1713)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_1712, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1713), u1_pre_topc(A_1713))), '#skF_4'))) | ~v1_funct_2(D_1712, u1_struct_0(g1_pre_topc(u1_struct_0(A_1713), u1_pre_topc(A_1713))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_1712, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1713), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_1712, u1_struct_0(A_1713), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_1712) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_1713) | ~v2_pre_topc(A_1713))), inference(superposition, [status(thm), theory('equality')], [c_17411, c_17841])).
% 23.01/12.00  tff(c_17971, plain, (![D_1715, A_1716]: (v5_pre_topc(D_1715, A_1716, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_1715, g1_pre_topc(u1_struct_0(A_1716), u1_pre_topc(A_1716)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(D_1715, u1_struct_0(g1_pre_topc(u1_struct_0(A_1716), u1_pre_topc(A_1716))), '#skF_4') | ~m1_subset_1(D_1715, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_1715, u1_struct_0(A_1716), '#skF_4') | ~v1_funct_1(D_1715) | ~l1_pre_topc(A_1716) | ~v2_pre_topc(A_1716))), inference(demodulation, [status(thm), theory('equality')], [c_12946, c_12882, c_17411, c_4490, c_17411, c_17411, c_4490, c_17847])).
% 23.01/12.00  tff(c_17980, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12934, c_17971])).
% 23.01/12.00  tff(c_17990, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_12810, c_4488, c_17431, c_17980])).
% 23.01/12.00  tff(c_17576, plain, (![D_1672, A_1673, B_1674]: (v5_pre_topc(D_1672, A_1673, B_1674) | ~v5_pre_topc(D_1672, A_1673, g1_pre_topc(u1_struct_0(B_1674), u1_pre_topc(B_1674))) | ~m1_subset_1(D_1672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1673), u1_struct_0(g1_pre_topc(u1_struct_0(B_1674), u1_pre_topc(B_1674)))))) | ~v1_funct_2(D_1672, u1_struct_0(A_1673), u1_struct_0(g1_pre_topc(u1_struct_0(B_1674), u1_pre_topc(B_1674)))) | ~m1_subset_1(D_1672, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1673), u1_struct_0(B_1674)))) | ~v1_funct_2(D_1672, u1_struct_0(A_1673), u1_struct_0(B_1674)) | ~v1_funct_1(D_1672) | ~l1_pre_topc(B_1674) | ~v2_pre_topc(B_1674) | ~l1_pre_topc(A_1673) | ~v2_pre_topc(A_1673))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_17592, plain, (![A_1673, B_1674]: (v5_pre_topc('#skF_4', A_1673, B_1674) | ~v5_pre_topc('#skF_4', A_1673, g1_pre_topc(u1_struct_0(B_1674), u1_pre_topc(B_1674))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1673), u1_struct_0(g1_pre_topc(u1_struct_0(B_1674), u1_pre_topc(B_1674)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1673), u1_struct_0(B_1674)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1673), u1_struct_0(B_1674)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1674) | ~v2_pre_topc(B_1674) | ~l1_pre_topc(A_1673) | ~v2_pre_topc(A_1673))), inference(resolution, [status(thm)], [c_4488, c_17576])).
% 23.01/12.00  tff(c_18291, plain, (![A_1740, B_1741]: (v5_pre_topc('#skF_4', A_1740, B_1741) | ~v5_pre_topc('#skF_4', A_1740, g1_pre_topc(u1_struct_0(B_1741), u1_pre_topc(B_1741))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1740), u1_struct_0(g1_pre_topc(u1_struct_0(B_1741), u1_pre_topc(B_1741)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1740), u1_struct_0(B_1741)) | ~l1_pre_topc(B_1741) | ~v2_pre_topc(B_1741) | ~l1_pre_topc(A_1740) | ~v2_pre_topc(A_1740))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4488, c_17592])).
% 23.01/12.00  tff(c_18309, plain, (![A_1740]: (v5_pre_topc('#skF_4', A_1740, '#skF_2') | ~v5_pre_topc('#skF_4', A_1740, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1740), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1740), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_1740) | ~v2_pre_topc(A_1740))), inference(superposition, [status(thm), theory('equality')], [c_12807, c_18291])).
% 23.01/12.00  tff(c_18384, plain, (![A_1744]: (v5_pre_topc('#skF_4', A_1744, '#skF_2') | ~v5_pre_topc('#skF_4', A_1744, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1744), '#skF_4') | ~l1_pre_topc(A_1744) | ~v2_pre_topc(A_1744))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_12807, c_17411, c_12807, c_18309])).
% 23.01/12.00  tff(c_18394, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_17990, c_18384])).
% 23.01/12.00  tff(c_18405, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_12810, c_18394])).
% 23.01/12.00  tff(c_18407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4482, c_18405])).
% 23.01/12.00  tff(c_18408, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_110])).
% 23.01/12.00  tff(c_18744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18672, c_18552, c_18408])).
% 23.01/12.00  tff(c_18745, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_18547])).
% 23.01/12.00  tff(c_18885, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18745, c_243])).
% 23.01/12.00  tff(c_18958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18885, c_18745, c_18408])).
% 23.01/12.00  tff(c_18960, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_108])).
% 23.01/12.00  tff(c_19449, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_19364, c_18960])).
% 23.01/12.00  tff(c_19121, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_80, c_19100])).
% 23.01/12.00  tff(c_19164, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_19121])).
% 23.01/12.00  tff(c_19398, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_19364, c_82])).
% 23.01/12.00  tff(c_19395, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_19364, c_80])).
% 23.01/12.00  tff(c_19605, plain, (![C_1911, A_1912, B_1913]: (v1_partfun1(C_1911, A_1912) | ~v1_funct_2(C_1911, A_1912, B_1913) | ~v1_funct_1(C_1911) | ~m1_subset_1(C_1911, k1_zfmisc_1(k2_zfmisc_1(A_1912, B_1913))) | v1_xboole_0(B_1913))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_19608, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_19395, c_19605])).
% 23.01/12.00  tff(c_19628, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_19398, c_19608])).
% 23.01/12.00  tff(c_19629, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_19164, c_19628])).
% 23.01/12.00  tff(c_19060, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_80, c_19039])).
% 23.01/12.00  tff(c_19178, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_19060, c_19175])).
% 23.01/12.00  tff(c_19187, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_19178])).
% 23.01/12.00  tff(c_19784, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_19629, c_19364, c_19364, c_19187])).
% 23.01/12.00  tff(c_19791, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_19784, c_19398])).
% 23.01/12.00  tff(c_19788, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_19784, c_19395])).
% 23.01/12.00  tff(c_21034, plain, (![D_2019, A_2020, B_2021]: (v5_pre_topc(D_2019, g1_pre_topc(u1_struct_0(A_2020), u1_pre_topc(A_2020)), B_2021) | ~v5_pre_topc(D_2019, A_2020, B_2021) | ~m1_subset_1(D_2019, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2020), u1_pre_topc(A_2020))), u1_struct_0(B_2021)))) | ~v1_funct_2(D_2019, u1_struct_0(g1_pre_topc(u1_struct_0(A_2020), u1_pre_topc(A_2020))), u1_struct_0(B_2021)) | ~m1_subset_1(D_2019, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2020), u1_struct_0(B_2021)))) | ~v1_funct_2(D_2019, u1_struct_0(A_2020), u1_struct_0(B_2021)) | ~v1_funct_1(D_2019) | ~l1_pre_topc(B_2021) | ~v2_pre_topc(B_2021) | ~l1_pre_topc(A_2020) | ~v2_pre_topc(A_2020))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_21043, plain, (![D_2019, B_2021]: (v5_pre_topc(D_2019, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2021) | ~v5_pre_topc(D_2019, '#skF_1', B_2021) | ~m1_subset_1(D_2019, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2021)))) | ~v1_funct_2(D_2019, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_2021)) | ~m1_subset_1(D_2019, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2021)))) | ~v1_funct_2(D_2019, u1_struct_0('#skF_1'), u1_struct_0(B_2021)) | ~v1_funct_1(D_2019) | ~l1_pre_topc(B_2021) | ~v2_pre_topc(B_2021) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19364, c_21034])).
% 23.01/12.00  tff(c_21430, plain, (![D_2053, B_2054]: (v5_pre_topc(D_2053, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_2054) | ~v5_pre_topc(D_2053, '#skF_1', B_2054) | ~m1_subset_1(D_2053, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_2054)))) | ~v1_funct_2(D_2053, k1_relat_1('#skF_4'), u1_struct_0(B_2054)) | ~v1_funct_1(D_2053) | ~l1_pre_topc(B_2054) | ~v2_pre_topc(B_2054))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_19364, c_19364, c_19784, c_19364, c_19784, c_19364, c_21043])).
% 23.01/12.00  tff(c_21433, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_19788, c_21430])).
% 23.01/12.00  tff(c_21453, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_19791, c_21433])).
% 23.01/12.00  tff(c_21454, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_19449, c_21453])).
% 23.01/12.00  tff(c_21464, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_21454])).
% 23.01/12.00  tff(c_21467, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_21464])).
% 23.01/12.00  tff(c_21471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_21467])).
% 23.01/12.00  tff(c_21472, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_21454])).
% 23.01/12.00  tff(c_21474, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_21472])).
% 23.01/12.00  tff(c_19397, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_19364, c_107])).
% 23.01/12.00  tff(c_19396, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_19364, c_111])).
% 23.01/12.00  tff(c_18959, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_108])).
% 23.01/12.00  tff(c_20980, plain, (![D_2016, A_2017, B_2018]: (v5_pre_topc(D_2016, A_2017, g1_pre_topc(u1_struct_0(B_2018), u1_pre_topc(B_2018))) | ~v5_pre_topc(D_2016, A_2017, B_2018) | ~m1_subset_1(D_2016, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2017), u1_struct_0(g1_pre_topc(u1_struct_0(B_2018), u1_pre_topc(B_2018)))))) | ~v1_funct_2(D_2016, u1_struct_0(A_2017), u1_struct_0(g1_pre_topc(u1_struct_0(B_2018), u1_pre_topc(B_2018)))) | ~m1_subset_1(D_2016, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2017), u1_struct_0(B_2018)))) | ~v1_funct_2(D_2016, u1_struct_0(A_2017), u1_struct_0(B_2018)) | ~v1_funct_1(D_2016) | ~l1_pre_topc(B_2018) | ~v2_pre_topc(B_2018) | ~l1_pre_topc(A_2017) | ~v2_pre_topc(A_2017))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_20989, plain, (![D_2016, B_2018]: (v5_pre_topc(D_2016, '#skF_1', g1_pre_topc(u1_struct_0(B_2018), u1_pre_topc(B_2018))) | ~v5_pre_topc(D_2016, '#skF_1', B_2018) | ~m1_subset_1(D_2016, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_2018), u1_pre_topc(B_2018)))))) | ~v1_funct_2(D_2016, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_2018), u1_pre_topc(B_2018)))) | ~m1_subset_1(D_2016, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_2018)))) | ~v1_funct_2(D_2016, u1_struct_0('#skF_1'), u1_struct_0(B_2018)) | ~v1_funct_1(D_2016) | ~l1_pre_topc(B_2018) | ~v2_pre_topc(B_2018) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_19364, c_20980])).
% 23.01/12.00  tff(c_21616, plain, (![D_2069, B_2070]: (v5_pre_topc(D_2069, '#skF_1', g1_pre_topc(u1_struct_0(B_2070), u1_pre_topc(B_2070))) | ~v5_pre_topc(D_2069, '#skF_1', B_2070) | ~m1_subset_1(D_2069, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_2070), u1_pre_topc(B_2070)))))) | ~v1_funct_2(D_2069, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_2070), u1_pre_topc(B_2070)))) | ~m1_subset_1(D_2069, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_2070)))) | ~v1_funct_2(D_2069, k1_relat_1('#skF_4'), u1_struct_0(B_2070)) | ~v1_funct_1(D_2069) | ~l1_pre_topc(B_2070) | ~v2_pre_topc(B_2070))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_19364, c_19364, c_19364, c_20989])).
% 23.01/12.00  tff(c_21622, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_19788, c_21616])).
% 23.01/12.00  tff(c_21641, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_19397, c_19396, c_19791, c_18959, c_21622])).
% 23.01/12.00  tff(c_21643, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21474, c_21641])).
% 23.01/12.00  tff(c_21644, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_21472])).
% 23.01/12.00  tff(c_21681, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_19036, c_21644])).
% 23.01/12.00  tff(c_21685, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_21681])).
% 23.01/12.00  tff(c_21686, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_19121])).
% 23.01/12.00  tff(c_21693, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_21686, c_144])).
% 23.01/12.00  tff(c_21709, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21693, c_21693, c_10])).
% 23.01/12.00  tff(c_21708, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_21693, c_20])).
% 23.01/12.00  tff(c_21904, plain, (![A_2091, B_2092, C_2093]: (k1_relset_1(A_2091, B_2092, C_2093)=k1_relat_1(C_2093) | ~m1_subset_1(C_2093, k1_zfmisc_1(k2_zfmisc_1(A_2091, B_2092))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_21919, plain, (![A_2091, B_2092]: (k1_relset_1(A_2091, B_2092, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_21708, c_21904])).
% 23.01/12.00  tff(c_22152, plain, (![C_2125, A_2126, B_2127]: (v1_funct_2(C_2125, A_2126, B_2127) | k1_relset_1(A_2126, B_2127, C_2125)!=A_2126 | ~m1_subset_1(C_2125, k1_zfmisc_1(k2_zfmisc_1(A_2126, B_2127))) | ~v1_funct_1(C_2125))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_22156, plain, (![A_2126, B_2127]: (v1_funct_2('#skF_4', A_2126, B_2127) | k1_relset_1(A_2126, B_2127, '#skF_4')!=A_2126 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_21708, c_22152])).
% 23.01/12.00  tff(c_22173, plain, (![A_2128, B_2129]: (v1_funct_2('#skF_4', A_2128, B_2129) | k1_relat_1('#skF_4')!=A_2128)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21919, c_22156])).
% 23.01/12.00  tff(c_21988, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_21693, c_21693, c_21693, c_113])).
% 23.01/12.00  tff(c_22179, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_22173, c_21988])).
% 23.01/12.00  tff(c_22183, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21708, c_22179])).
% 23.01/12.00  tff(c_22184, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_22183])).
% 23.01/12.00  tff(c_22169, plain, (![A_2126, B_2127]: (v1_funct_2('#skF_4', A_2126, B_2127) | k1_relat_1('#skF_4')!=A_2126)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21919, c_22156])).
% 23.01/12.00  tff(c_22244, plain, (![C_2137, A_2138, B_2139]: (~v1_xboole_0(C_2137) | ~v1_funct_2(C_2137, A_2138, B_2139) | ~v1_funct_1(C_2137) | ~m1_subset_1(C_2137, k1_zfmisc_1(k2_zfmisc_1(A_2138, B_2139))) | v1_xboole_0(B_2139) | v1_xboole_0(A_2138))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_22248, plain, (![A_2138, B_2139]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_2138, B_2139) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_2139) | v1_xboole_0(A_2138))), inference(resolution, [status(thm)], [c_21708, c_22244])).
% 23.01/12.00  tff(c_22265, plain, (![A_2140, B_2141]: (~v1_funct_2('#skF_4', A_2140, B_2141) | v1_xboole_0(B_2141) | v1_xboole_0(A_2140))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21686, c_22248])).
% 23.01/12.00  tff(c_22274, plain, (![B_2127, A_2126]: (v1_xboole_0(B_2127) | v1_xboole_0(A_2126) | k1_relat_1('#skF_4')!=A_2126)), inference(resolution, [status(thm)], [c_22169, c_22265])).
% 23.01/12.00  tff(c_22276, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_22274])).
% 23.01/12.00  tff(c_22040, plain, (![C_2120, A_2121, B_2122]: (v1_partfun1(C_2120, A_2121) | ~v1_funct_2(C_2120, A_2121, B_2122) | ~v1_funct_1(C_2120) | ~m1_subset_1(C_2120, k1_zfmisc_1(k2_zfmisc_1(A_2121, B_2122))) | v1_xboole_0(B_2122))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_22044, plain, (![A_2121, B_2122]: (v1_partfun1('#skF_4', A_2121) | ~v1_funct_2('#skF_4', A_2121, B_2122) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_2122))), inference(resolution, [status(thm)], [c_21708, c_22040])).
% 23.01/12.00  tff(c_22060, plain, (![A_2123, B_2124]: (v1_partfun1('#skF_4', A_2123) | ~v1_funct_2('#skF_4', A_2123, B_2124) | v1_xboole_0(B_2124))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22044])).
% 23.01/12.00  tff(c_22066, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_22060])).
% 23.01/12.00  tff(c_22071, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_19128, c_22066])).
% 23.01/12.00  tff(c_19063, plain, (![A_1834]: (v4_relat_1(k1_xboole_0, A_1834))), inference(resolution, [status(thm)], [c_20, c_19039])).
% 23.01/12.00  tff(c_21698, plain, (![A_1834]: (v4_relat_1('#skF_4', A_1834))), inference(demodulation, [status(thm), theory('equality')], [c_21693, c_19063])).
% 23.01/12.00  tff(c_21862, plain, (![B_2085, A_2086]: (k1_relat_1(B_2085)=A_2086 | ~v1_partfun1(B_2085, A_2086) | ~v4_relat_1(B_2085, A_2086) | ~v1_relat_1(B_2085))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_21865, plain, (![A_1834]: (k1_relat_1('#skF_4')=A_1834 | ~v1_partfun1('#skF_4', A_1834) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_21698, c_21862])).
% 23.01/12.00  tff(c_21868, plain, (![A_1834]: (k1_relat_1('#skF_4')=A_1834 | ~v1_partfun1('#skF_4', A_1834))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_21865])).
% 23.01/12.00  tff(c_22075, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22071, c_21868])).
% 23.01/12.00  tff(c_19141, plain, (![A_1850, C_1851, B_1852]: (m1_subset_1(A_1850, C_1851) | ~m1_subset_1(B_1852, k1_zfmisc_1(C_1851)) | ~r2_hidden(A_1850, B_1852))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.01/12.00  tff(c_19153, plain, (![A_1850, A_45]: (m1_subset_1(A_1850, k1_zfmisc_1(u1_struct_0(A_45))) | ~r2_hidden(A_1850, u1_pre_topc(A_45)) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_19141])).
% 23.01/12.00  tff(c_22087, plain, (![A_1850]: (m1_subset_1(A_1850, k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~r2_hidden(A_1850, u1_pre_topc('#skF_1')) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22075, c_19153])).
% 23.01/12.00  tff(c_22231, plain, (![A_2136]: (m1_subset_1(A_2136, k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~r2_hidden(A_2136, u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_22087])).
% 23.01/12.00  tff(c_22241, plain, (![A_2136]: (v1_xboole_0(A_2136) | ~v1_xboole_0(k1_relat_1('#skF_4')) | ~r2_hidden(A_2136, u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_22231, c_22])).
% 23.01/12.00  tff(c_22243, plain, (~v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_22241])).
% 23.01/12.00  tff(c_22279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22276, c_22243])).
% 23.01/12.00  tff(c_22280, plain, (![B_2127]: (v1_xboole_0(B_2127))), inference(splitRight, [status(thm)], [c_22274])).
% 23.01/12.00  tff(c_22332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22280, c_22243])).
% 23.01/12.00  tff(c_22334, plain, (v1_xboole_0(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_22241])).
% 23.01/12.00  tff(c_21694, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_21686, c_4])).
% 23.01/12.00  tff(c_22337, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_22334, c_21694])).
% 23.01/12.00  tff(c_22343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22184, c_22337])).
% 23.01/12.00  tff(c_22345, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_22183])).
% 23.01/12.00  tff(c_18961, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_22079, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22075, c_18961])).
% 23.01/12.00  tff(c_22355, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22345, c_22079])).
% 23.01/12.00  tff(c_22362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_21686, c_21709, c_22355])).
% 23.01/12.00  tff(c_22363, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_19122])).
% 23.01/12.00  tff(c_22370, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22363, c_144])).
% 23.01/12.00  tff(c_22402, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22370, c_22370, c_8])).
% 23.01/12.00  tff(c_22364, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_19122])).
% 23.01/12.00  tff(c_22470, plain, (![A_2149]: (A_2149='#skF_4' | ~v1_xboole_0(A_2149))), inference(demodulation, [status(thm), theory('equality')], [c_22370, c_144])).
% 23.01/12.00  tff(c_22477, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_22364, c_22470])).
% 23.01/12.00  tff(c_22490, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22477, c_18961])).
% 23.01/12.00  tff(c_22498, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22363, c_22402, c_22490])).
% 23.01/12.00  tff(c_22500, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_22499, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_22507, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_22499, c_4])).
% 23.01/12.00  tff(c_22593, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_22500, c_22507])).
% 23.01/12.00  tff(c_22506, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_22499, c_144])).
% 23.01/12.00  tff(c_22649, plain, (![B_2165, A_2166]: (B_2165='#skF_4' | A_2166='#skF_4' | k2_zfmisc_1(A_2166, B_2165)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22506, c_22506, c_22506, c_6])).
% 23.01/12.00  tff(c_22659, plain, (u1_struct_0('#skF_2')='#skF_4' | u1_struct_0('#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_22593, c_22649])).
% 23.01/12.00  tff(c_22664, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitLeft, [status(thm)], [c_22659])).
% 23.01/12.00  tff(c_22830, plain, (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_22664, c_18960])).
% 23.01/12.00  tff(c_22711, plain, (![A_2169, B_2170]: (l1_pre_topc(g1_pre_topc(A_2169, B_2170)) | ~m1_subset_1(B_2170, k1_zfmisc_1(k1_zfmisc_1(A_2169))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/12.00  tff(c_22727, plain, (![A_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_45), u1_pre_topc(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_22711])).
% 23.01/12.00  tff(c_22668, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_22664, c_82])).
% 23.01/12.00  tff(c_22513, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_22506, c_20])).
% 23.01/12.00  tff(c_25702, plain, (![C_2460, A_2461, B_2462]: (v1_partfun1(C_2460, A_2461) | ~v1_funct_2(C_2460, A_2461, B_2462) | ~v1_funct_1(C_2460) | ~m1_subset_1(C_2460, k1_zfmisc_1(k2_zfmisc_1(A_2461, B_2462))) | v1_xboole_0(B_2462))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_25706, plain, (![A_2461, B_2462]: (v1_partfun1('#skF_4', A_2461) | ~v1_funct_2('#skF_4', A_2461, B_2462) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_2462))), inference(resolution, [status(thm)], [c_22513, c_25702])).
% 23.01/12.00  tff(c_25722, plain, (![A_2463, B_2464]: (v1_partfun1('#skF_4', A_2463) | ~v1_funct_2('#skF_4', A_2463, B_2464) | v1_xboole_0(B_2464))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_25706])).
% 23.01/12.00  tff(c_25730, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_22668, c_25722])).
% 23.01/12.00  tff(c_25738, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_25730])).
% 23.01/12.00  tff(c_25795, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(resolution, [status(thm)], [c_25738, c_22507])).
% 23.01/12.00  tff(c_25816, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_25795, c_22727])).
% 23.01/12.00  tff(c_25961, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_25816])).
% 23.01/12.00  tff(c_25964, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22727, c_25961])).
% 23.01/12.00  tff(c_25968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_25964])).
% 23.01/12.00  tff(c_25970, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_25816])).
% 23.01/12.00  tff(c_25810, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_25795, c_66])).
% 23.01/12.00  tff(c_26457, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_25970, c_25810])).
% 23.01/12.00  tff(c_26458, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_26457])).
% 23.01/12.00  tff(c_26461, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_26458])).
% 23.01/12.00  tff(c_26465, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_26461])).
% 23.01/12.00  tff(c_26467, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_26457])).
% 23.01/12.00  tff(c_22667, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22664, c_107])).
% 23.01/12.00  tff(c_25595, plain, (![C_2441, B_2442]: (v1_partfun1(C_2441, '#skF_4') | ~v1_funct_2(C_2441, '#skF_4', B_2442) | ~m1_subset_1(C_2441, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_2441))), inference(demodulation, [status(thm), theory('equality')], [c_22506, c_22506, c_22506, c_113])).
% 23.01/12.00  tff(c_25597, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22667, c_25595])).
% 23.01/12.00  tff(c_25600, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_25597])).
% 23.01/12.00  tff(c_22731, plain, (![C_2172, A_2173, B_2174]: (v4_relat_1(C_2172, A_2173) | ~m1_subset_1(C_2172, k1_zfmisc_1(k2_zfmisc_1(A_2173, B_2174))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/12.00  tff(c_22746, plain, (![A_2173]: (v4_relat_1('#skF_4', A_2173))), inference(resolution, [status(thm)], [c_22513, c_22731])).
% 23.01/12.00  tff(c_22863, plain, (![B_2195, A_2196]: (k1_relat_1(B_2195)=A_2196 | ~v1_partfun1(B_2195, A_2196) | ~v4_relat_1(B_2195, A_2196) | ~v1_relat_1(B_2195))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_22866, plain, (![A_2173]: (k1_relat_1('#skF_4')=A_2173 | ~v1_partfun1('#skF_4', A_2173) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22746, c_22863])).
% 23.01/12.00  tff(c_22869, plain, (![A_2173]: (k1_relat_1('#skF_4')=A_2173 | ~v1_partfun1('#skF_4', A_2173))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_22866])).
% 23.01/12.00  tff(c_25604, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_25600, c_22869])).
% 23.01/12.00  tff(c_22888, plain, (![A_2206, B_2207, C_2208]: (k1_relset_1(A_2206, B_2207, C_2208)=k1_relat_1(C_2208) | ~m1_subset_1(C_2208, k1_zfmisc_1(k2_zfmisc_1(A_2206, B_2207))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_22903, plain, (![A_2206, B_2207]: (k1_relset_1(A_2206, B_2207, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22513, c_22888])).
% 23.01/12.00  tff(c_25605, plain, (![C_2443, A_2444, B_2445]: (v1_funct_2(C_2443, A_2444, B_2445) | k1_relset_1(A_2444, B_2445, C_2443)!=A_2444 | ~m1_subset_1(C_2443, k1_zfmisc_1(k2_zfmisc_1(A_2444, B_2445))) | ~v1_funct_1(C_2443))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_25609, plain, (![A_2444, B_2445]: (v1_funct_2('#skF_4', A_2444, B_2445) | k1_relset_1(A_2444, B_2445, '#skF_4')!=A_2444 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22513, c_25605])).
% 23.01/12.00  tff(c_25622, plain, (![A_2444, B_2445]: (v1_funct_2('#skF_4', A_2444, B_2445) | k1_relat_1('#skF_4')!=A_2444)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22903, c_25609])).
% 23.01/12.00  tff(c_25672, plain, (![B_2445]: (v1_funct_2('#skF_4', '#skF_4', B_2445))), inference(demodulation, [status(thm), theory('equality')], [c_25604, c_25622])).
% 23.01/12.00  tff(c_26237, plain, (![D_2512, A_2513, B_2514]: (v5_pre_topc(D_2512, A_2513, g1_pre_topc(u1_struct_0(B_2514), u1_pre_topc(B_2514))) | ~v5_pre_topc(D_2512, A_2513, B_2514) | ~m1_subset_1(D_2512, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2513), u1_struct_0(g1_pre_topc(u1_struct_0(B_2514), u1_pre_topc(B_2514)))))) | ~v1_funct_2(D_2512, u1_struct_0(A_2513), u1_struct_0(g1_pre_topc(u1_struct_0(B_2514), u1_pre_topc(B_2514)))) | ~m1_subset_1(D_2512, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2513), u1_struct_0(B_2514)))) | ~v1_funct_2(D_2512, u1_struct_0(A_2513), u1_struct_0(B_2514)) | ~v1_funct_1(D_2512) | ~l1_pre_topc(B_2514) | ~v2_pre_topc(B_2514) | ~l1_pre_topc(A_2513) | ~v2_pre_topc(A_2513))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_26262, plain, (![A_2513, B_2514]: (v5_pre_topc('#skF_4', A_2513, g1_pre_topc(u1_struct_0(B_2514), u1_pre_topc(B_2514))) | ~v5_pre_topc('#skF_4', A_2513, B_2514) | ~v1_funct_2('#skF_4', u1_struct_0(A_2513), u1_struct_0(g1_pre_topc(u1_struct_0(B_2514), u1_pre_topc(B_2514)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2513), u1_struct_0(B_2514)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2513), u1_struct_0(B_2514)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_2514) | ~v2_pre_topc(B_2514) | ~l1_pre_topc(A_2513) | ~v2_pre_topc(A_2513))), inference(resolution, [status(thm)], [c_22513, c_26237])).
% 23.01/12.00  tff(c_26469, plain, (![A_2519, B_2520]: (v5_pre_topc('#skF_4', A_2519, g1_pre_topc(u1_struct_0(B_2520), u1_pre_topc(B_2520))) | ~v5_pre_topc('#skF_4', A_2519, B_2520) | ~v1_funct_2('#skF_4', u1_struct_0(A_2519), u1_struct_0(g1_pre_topc(u1_struct_0(B_2520), u1_pre_topc(B_2520)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2519), u1_struct_0(B_2520)) | ~l1_pre_topc(B_2520) | ~v2_pre_topc(B_2520) | ~l1_pre_topc(A_2519) | ~v2_pre_topc(A_2519))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_26262])).
% 23.01/12.00  tff(c_26493, plain, (![B_2520]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2520), u1_pre_topc(B_2520))) | ~v5_pre_topc('#skF_4', '#skF_1', B_2520) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_2520), u1_pre_topc(B_2520)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2520)) | ~l1_pre_topc(B_2520) | ~v2_pre_topc(B_2520) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22664, c_26469])).
% 23.01/12.00  tff(c_26511, plain, (![B_2520]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2520), u1_pre_topc(B_2520))) | ~v5_pre_topc('#skF_4', '#skF_1', B_2520) | ~l1_pre_topc(B_2520) | ~v2_pre_topc(B_2520))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_25672, c_22664, c_25672, c_26493])).
% 23.01/12.00  tff(c_26515, plain, (![B_2521]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2521), u1_pre_topc(B_2521))) | ~v5_pre_topc('#skF_4', '#skF_1', B_2521) | ~l1_pre_topc(B_2521) | ~v2_pre_topc(B_2521))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_25672, c_22664, c_25672, c_26493])).
% 23.01/12.00  tff(c_26524, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_25795, c_26515])).
% 23.01/12.00  tff(c_26536, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26467, c_25970, c_26524])).
% 23.01/12.00  tff(c_26543, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_26536])).
% 23.01/12.00  tff(c_26546, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26511, c_26543])).
% 23.01/12.00  tff(c_26550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_18959, c_26546])).
% 23.01/12.00  tff(c_26552, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_26536])).
% 23.01/12.00  tff(c_25651, plain, (![B_2449, C_2450, A_2451]: (B_2449='#skF_4' | v1_partfun1(C_2450, A_2451) | ~v1_funct_2(C_2450, A_2451, B_2449) | ~m1_subset_1(C_2450, k1_zfmisc_1(k2_zfmisc_1(A_2451, B_2449))) | ~v1_funct_1(C_2450))), inference(demodulation, [status(thm), theory('equality')], [c_22506, c_58])).
% 23.01/12.00  tff(c_25655, plain, (![B_2449, A_2451]: (B_2449='#skF_4' | v1_partfun1('#skF_4', A_2451) | ~v1_funct_2('#skF_4', A_2451, B_2449) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22513, c_25651])).
% 23.01/12.00  tff(c_25681, plain, (![B_2454, A_2455]: (B_2454='#skF_4' | v1_partfun1('#skF_4', A_2455) | ~v1_funct_2('#skF_4', A_2455, B_2454))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_25655])).
% 23.01/12.00  tff(c_25689, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_22668, c_25681])).
% 23.01/12.00  tff(c_25737, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_25689])).
% 23.01/12.00  tff(c_25625, plain, (![A_2173]: (A_2173='#skF_4' | ~v1_partfun1('#skF_4', A_2173))), inference(demodulation, [status(thm), theory('equality')], [c_25604, c_22869])).
% 23.01/12.00  tff(c_25742, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_25737, c_25625])).
% 23.01/12.00  tff(c_25910, plain, (![D_2477, A_2478, B_2479]: (v5_pre_topc(D_2477, g1_pre_topc(u1_struct_0(A_2478), u1_pre_topc(A_2478)), B_2479) | ~v5_pre_topc(D_2477, A_2478, B_2479) | ~m1_subset_1(D_2477, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2478), u1_pre_topc(A_2478))), u1_struct_0(B_2479)))) | ~v1_funct_2(D_2477, u1_struct_0(g1_pre_topc(u1_struct_0(A_2478), u1_pre_topc(A_2478))), u1_struct_0(B_2479)) | ~m1_subset_1(D_2477, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2478), u1_struct_0(B_2479)))) | ~v1_funct_2(D_2477, u1_struct_0(A_2478), u1_struct_0(B_2479)) | ~v1_funct_1(D_2477) | ~l1_pre_topc(B_2479) | ~v2_pre_topc(B_2479) | ~l1_pre_topc(A_2478) | ~v2_pre_topc(A_2478))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_25935, plain, (![A_2478, B_2479]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2478), u1_pre_topc(A_2478)), B_2479) | ~v5_pre_topc('#skF_4', A_2478, B_2479) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2478), u1_pre_topc(A_2478))), u1_struct_0(B_2479)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2478), u1_struct_0(B_2479)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2478), u1_struct_0(B_2479)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_2479) | ~v2_pre_topc(B_2479) | ~l1_pre_topc(A_2478) | ~v2_pre_topc(A_2478))), inference(resolution, [status(thm)], [c_22513, c_25910])).
% 23.01/12.00  tff(c_26691, plain, (![A_2533, B_2534]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2533), u1_pre_topc(A_2533)), B_2534) | ~v5_pre_topc('#skF_4', A_2533, B_2534) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2533), u1_pre_topc(A_2533))), u1_struct_0(B_2534)) | ~v1_funct_2('#skF_4', u1_struct_0(A_2533), u1_struct_0(B_2534)) | ~l1_pre_topc(B_2534) | ~v2_pre_topc(B_2534) | ~l1_pre_topc(A_2533) | ~v2_pre_topc(A_2533))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_25935])).
% 23.01/12.00  tff(c_26715, plain, (![B_2534]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2534) | ~v5_pre_topc('#skF_4', '#skF_1', B_2534) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_2534)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2534)) | ~l1_pre_topc(B_2534) | ~v2_pre_topc(B_2534) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22664, c_26691])).
% 23.01/12.00  tff(c_26736, plain, (![B_2535]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_2535) | ~v5_pre_topc('#skF_4', '#skF_1', B_2535) | ~l1_pre_topc(B_2535) | ~v2_pre_topc(B_2535))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_25672, c_22664, c_25672, c_25742, c_22664, c_26715])).
% 23.01/12.00  tff(c_26742, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_26736, c_22830])).
% 23.01/12.00  tff(c_26747, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26467, c_25970, c_26552, c_26742])).
% 23.01/12.00  tff(c_26748, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_25689])).
% 23.01/12.00  tff(c_26768, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26748, c_22727])).
% 23.01/12.00  tff(c_26902, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_26768])).
% 23.01/12.00  tff(c_26910, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22727, c_26902])).
% 23.01/12.00  tff(c_26914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_26910])).
% 23.01/12.00  tff(c_26916, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_26768])).
% 23.01/12.00  tff(c_26762, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26748, c_66])).
% 23.01/12.00  tff(c_27218, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_26916, c_26762])).
% 23.01/12.00  tff(c_27219, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_27218])).
% 23.01/12.00  tff(c_27222, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_27219])).
% 23.01/12.00  tff(c_27226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_27222])).
% 23.01/12.00  tff(c_27228, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_27218])).
% 23.01/12.00  tff(c_26750, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26748, c_22668])).
% 23.01/12.00  tff(c_26968, plain, (![D_2558, A_2559, B_2560]: (v5_pre_topc(D_2558, A_2559, g1_pre_topc(u1_struct_0(B_2560), u1_pre_topc(B_2560))) | ~v5_pre_topc(D_2558, A_2559, B_2560) | ~m1_subset_1(D_2558, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2559), u1_struct_0(g1_pre_topc(u1_struct_0(B_2560), u1_pre_topc(B_2560)))))) | ~v1_funct_2(D_2558, u1_struct_0(A_2559), u1_struct_0(g1_pre_topc(u1_struct_0(B_2560), u1_pre_topc(B_2560)))) | ~m1_subset_1(D_2558, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2559), u1_struct_0(B_2560)))) | ~v1_funct_2(D_2558, u1_struct_0(A_2559), u1_struct_0(B_2560)) | ~v1_funct_1(D_2558) | ~l1_pre_topc(B_2560) | ~v2_pre_topc(B_2560) | ~l1_pre_topc(A_2559) | ~v2_pre_topc(A_2559))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_26987, plain, (![A_2559, B_2560]: (v5_pre_topc('#skF_4', A_2559, g1_pre_topc(u1_struct_0(B_2560), u1_pre_topc(B_2560))) | ~v5_pre_topc('#skF_4', A_2559, B_2560) | ~v1_funct_2('#skF_4', u1_struct_0(A_2559), u1_struct_0(g1_pre_topc(u1_struct_0(B_2560), u1_pre_topc(B_2560)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2559), u1_struct_0(B_2560)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2559), u1_struct_0(B_2560)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_2560) | ~v2_pre_topc(B_2560) | ~l1_pre_topc(A_2559) | ~v2_pre_topc(A_2559))), inference(resolution, [status(thm)], [c_22513, c_26968])).
% 23.01/12.00  tff(c_27387, plain, (![A_2597, B_2598]: (v5_pre_topc('#skF_4', A_2597, g1_pre_topc(u1_struct_0(B_2598), u1_pre_topc(B_2598))) | ~v5_pre_topc('#skF_4', A_2597, B_2598) | ~v1_funct_2('#skF_4', u1_struct_0(A_2597), u1_struct_0(g1_pre_topc(u1_struct_0(B_2598), u1_pre_topc(B_2598)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2597), u1_struct_0(B_2598)) | ~l1_pre_topc(B_2598) | ~v2_pre_topc(B_2598) | ~l1_pre_topc(A_2597) | ~v2_pre_topc(A_2597))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_26987])).
% 23.01/12.00  tff(c_27405, plain, (![B_2598]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2598), u1_pre_topc(B_2598))) | ~v5_pre_topc('#skF_4', '#skF_1', B_2598) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_2598), u1_pre_topc(B_2598)))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2598)) | ~l1_pre_topc(B_2598) | ~v2_pre_topc(B_2598) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22664, c_27387])).
% 23.01/12.00  tff(c_27419, plain, (![B_2598]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2598), u1_pre_topc(B_2598))) | ~v5_pre_topc('#skF_4', '#skF_1', B_2598) | ~l1_pre_topc(B_2598) | ~v2_pre_topc(B_2598))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_25672, c_22664, c_25672, c_27405])).
% 23.01/12.00  tff(c_22831, plain, (![A_2188, C_2189, B_2190]: (m1_subset_1(A_2188, C_2189) | ~m1_subset_1(B_2190, k1_zfmisc_1(C_2189)) | ~r2_hidden(A_2188, B_2190))), inference(cnfTransformation, [status(thm)], [f_68])).
% 23.01/12.00  tff(c_22842, plain, (![A_2188, A_45]: (m1_subset_1(A_2188, k1_zfmisc_1(u1_struct_0(A_45))) | ~r2_hidden(A_2188, u1_pre_topc(A_45)) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_22831])).
% 23.01/12.00  tff(c_26756, plain, (![A_2188]: (m1_subset_1(A_2188, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_2188, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_26748, c_22842])).
% 23.01/12.00  tff(c_27122, plain, (![A_2573]: (m1_subset_1(A_2573, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_2573, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(demodulation, [status(thm), theory('equality')], [c_26916, c_26756])).
% 23.01/12.00  tff(c_27127, plain, (![B_6]: (m1_subset_1(B_6, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(B_6, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(resolution, [status(thm)], [c_14, c_27122])).
% 23.01/12.00  tff(c_27269, plain, (v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_27127])).
% 23.01/12.00  tff(c_27281, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(resolution, [status(thm)], [c_27269, c_22507])).
% 23.01/12.00  tff(c_27423, plain, (![B_2599]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_2599), u1_pre_topc(B_2599))) | ~v5_pre_topc('#skF_4', '#skF_1', B_2599) | ~l1_pre_topc(B_2599) | ~v2_pre_topc(B_2599))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_25672, c_22664, c_25672, c_27405])).
% 23.01/12.00  tff(c_27429, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26748, c_27423])).
% 23.01/12.00  tff(c_27436, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27228, c_26916, c_27281, c_27429])).
% 23.01/12.00  tff(c_27439, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_27436])).
% 23.01/12.00  tff(c_27442, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_27419, c_27439])).
% 23.01/12.00  tff(c_27446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_18959, c_27442])).
% 23.01/12.00  tff(c_27448, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_27436])).
% 23.01/12.00  tff(c_27057, plain, (![D_2566, A_2567, B_2568]: (v5_pre_topc(D_2566, g1_pre_topc(u1_struct_0(A_2567), u1_pre_topc(A_2567)), B_2568) | ~v5_pre_topc(D_2566, A_2567, B_2568) | ~m1_subset_1(D_2566, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2567), u1_pre_topc(A_2567))), u1_struct_0(B_2568)))) | ~v1_funct_2(D_2566, u1_struct_0(g1_pre_topc(u1_struct_0(A_2567), u1_pre_topc(A_2567))), u1_struct_0(B_2568)) | ~m1_subset_1(D_2566, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2567), u1_struct_0(B_2568)))) | ~v1_funct_2(D_2566, u1_struct_0(A_2567), u1_struct_0(B_2568)) | ~v1_funct_1(D_2566) | ~l1_pre_topc(B_2568) | ~v2_pre_topc(B_2568) | ~l1_pre_topc(A_2567) | ~v2_pre_topc(A_2567))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_27076, plain, (![A_2567, B_2568]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2567), u1_pre_topc(A_2567)), B_2568) | ~v5_pre_topc('#skF_4', A_2567, B_2568) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2567), u1_pre_topc(A_2567))), u1_struct_0(B_2568)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2567), u1_struct_0(B_2568)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_2567), u1_struct_0(B_2568)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_2568) | ~v2_pre_topc(B_2568) | ~l1_pre_topc(A_2567) | ~v2_pre_topc(A_2567))), inference(resolution, [status(thm)], [c_22513, c_27057])).
% 23.01/12.00  tff(c_27239, plain, (![A_2593, B_2594]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_2593), u1_pre_topc(A_2593)), B_2594) | ~v5_pre_topc('#skF_4', A_2593, B_2594) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_2593), u1_pre_topc(A_2593))), u1_struct_0(B_2594)) | ~v1_funct_2('#skF_4', u1_struct_0(A_2593), u1_struct_0(B_2594)) | ~l1_pre_topc(B_2594) | ~v2_pre_topc(B_2594) | ~l1_pre_topc(A_2593) | ~v2_pre_topc(A_2593))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_27076])).
% 23.01/12.00  tff(c_27254, plain, (![B_2594]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_2594) | ~v5_pre_topc('#skF_4', '#skF_1', B_2594) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_2594)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_2594)) | ~l1_pre_topc(B_2594) | ~v2_pre_topc(B_2594) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22664, c_27239])).
% 23.01/12.00  tff(c_27896, plain, (![B_2621]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), B_2621) | ~v5_pre_topc('#skF_4', '#skF_1', B_2621) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_2621)) | ~l1_pre_topc(B_2621) | ~v2_pre_topc(B_2621))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_25672, c_22664, c_22664, c_27254])).
% 23.01/12.00  tff(c_27899, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_26748, c_27896])).
% 23.01/12.00  tff(c_27907, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27228, c_26916, c_26750, c_27448, c_27899])).
% 23.01/12.00  tff(c_27909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22830, c_27907])).
% 23.01/12.00  tff(c_27910, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_22659])).
% 23.01/12.00  tff(c_27914, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27910, c_107])).
% 23.01/12.00  tff(c_37502, plain, (![A_3505, B_3506, C_3507]: (k1_relset_1(A_3505, B_3506, C_3507)=k1_relat_1(C_3507) | ~m1_subset_1(C_3507, k1_zfmisc_1(k2_zfmisc_1(A_3505, B_3506))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_37517, plain, (![A_3505, B_3506]: (k1_relset_1(A_3505, B_3506, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22513, c_37502])).
% 23.01/12.00  tff(c_39008, plain, (![C_3689, A_3690, B_3691]: (v1_funct_2(C_3689, A_3690, B_3691) | k1_relset_1(A_3690, B_3691, C_3689)!=A_3690 | ~m1_subset_1(C_3689, k1_zfmisc_1(k2_zfmisc_1(A_3690, B_3691))) | ~v1_funct_1(C_3689))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_39012, plain, (![A_3690, B_3691]: (v1_funct_2('#skF_4', A_3690, B_3691) | k1_relset_1(A_3690, B_3691, '#skF_4')!=A_3690 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_22513, c_39008])).
% 23.01/12.00  tff(c_39025, plain, (![A_3690, B_3691]: (v1_funct_2('#skF_4', A_3690, B_3691) | k1_relat_1('#skF_4')!=A_3690)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_37517, c_39012])).
% 23.01/12.00  tff(c_39077, plain, (![C_3699, A_3700, B_3701]: (~v1_xboole_0(C_3699) | ~v1_funct_2(C_3699, A_3700, B_3701) | ~v1_funct_1(C_3699) | ~m1_subset_1(C_3699, k1_zfmisc_1(k2_zfmisc_1(A_3700, B_3701))) | v1_xboole_0(B_3701) | v1_xboole_0(A_3700))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_39081, plain, (![A_3700, B_3701]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_3700, B_3701) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_3701) | v1_xboole_0(A_3700))), inference(resolution, [status(thm)], [c_22513, c_39077])).
% 23.01/12.00  tff(c_39098, plain, (![A_3702, B_3703]: (~v1_funct_2('#skF_4', A_3702, B_3703) | v1_xboole_0(B_3703) | v1_xboole_0(A_3702))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22499, c_39081])).
% 23.01/12.00  tff(c_39105, plain, (![B_3691, A_3690]: (v1_xboole_0(B_3691) | v1_xboole_0(A_3690) | k1_relat_1('#skF_4')!=A_3690)), inference(resolution, [status(thm)], [c_39025, c_39098])).
% 23.01/12.00  tff(c_39110, plain, (![A_3704]: (v1_xboole_0(A_3704) | k1_relat_1('#skF_4')!=A_3704)), inference(splitLeft, [status(thm)], [c_39105])).
% 23.01/12.00  tff(c_39169, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_39110, c_22507])).
% 23.01/12.00  tff(c_39029, plain, (![A_3692, B_3693]: (v1_funct_2('#skF_4', A_3692, B_3693) | k1_relat_1('#skF_4')!=A_3692)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_37517, c_39012])).
% 23.01/12.00  tff(c_37610, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_22506, c_22506, c_22506, c_113])).
% 23.01/12.00  tff(c_39035, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_39029, c_37610])).
% 23.01/12.00  tff(c_39042, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_39035])).
% 23.01/12.00  tff(c_39044, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_39042])).
% 23.01/12.00  tff(c_39183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39169, c_39044])).
% 23.01/12.00  tff(c_39184, plain, (![B_3691]: (v1_xboole_0(B_3691))), inference(splitRight, [status(thm)], [c_39105])).
% 23.01/12.00  tff(c_22515, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22506, c_22506, c_8])).
% 23.01/12.00  tff(c_27915, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_27910, c_82])).
% 23.01/12.00  tff(c_37542, plain, (![C_3513, A_3514, B_3515]: (v1_partfun1(C_3513, A_3514) | ~v1_funct_2(C_3513, A_3514, B_3515) | ~v1_funct_1(C_3513) | ~m1_subset_1(C_3513, k1_zfmisc_1(k2_zfmisc_1(A_3514, B_3515))) | v1_xboole_0(B_3515))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_37546, plain, (![A_3514, B_3515]: (v1_partfun1('#skF_4', A_3514) | ~v1_funct_2('#skF_4', A_3514, B_3515) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_3515))), inference(resolution, [status(thm)], [c_22513, c_37542])).
% 23.01/12.00  tff(c_37562, plain, (![A_3516, B_3517]: (v1_partfun1('#skF_4', A_3516) | ~v1_funct_2('#skF_4', A_3516, B_3517) | v1_xboole_0(B_3517))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_37546])).
% 23.01/12.00  tff(c_37569, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_27915, c_37562])).
% 23.01/12.00  tff(c_37627, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_37569])).
% 23.01/12.00  tff(c_37640, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))='#skF_4'), inference(resolution, [status(thm)], [c_37627, c_22507])).
% 23.01/12.00  tff(c_38136, plain, (![D_3573, A_3574, B_3575]: (v5_pre_topc(D_3573, A_3574, g1_pre_topc(u1_struct_0(B_3575), u1_pre_topc(B_3575))) | ~v5_pre_topc(D_3573, A_3574, B_3575) | ~m1_subset_1(D_3573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574), u1_struct_0(g1_pre_topc(u1_struct_0(B_3575), u1_pre_topc(B_3575)))))) | ~v1_funct_2(D_3573, u1_struct_0(A_3574), u1_struct_0(g1_pre_topc(u1_struct_0(B_3575), u1_pre_topc(B_3575)))) | ~m1_subset_1(D_3573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574), u1_struct_0(B_3575)))) | ~v1_funct_2(D_3573, u1_struct_0(A_3574), u1_struct_0(B_3575)) | ~v1_funct_1(D_3573) | ~l1_pre_topc(B_3575) | ~v2_pre_topc(B_3575) | ~l1_pre_topc(A_3574) | ~v2_pre_topc(A_3574))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_38148, plain, (![D_3573, A_3574]: (v5_pre_topc(D_3573, A_3574, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_3573, A_3574, '#skF_2') | ~m1_subset_1(D_3573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_3573, u1_struct_0(A_3574), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_3573, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3574), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_3573, u1_struct_0(A_3574), u1_struct_0('#skF_2')) | ~v1_funct_1(D_3573) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_3574) | ~v2_pre_topc(A_3574))), inference(superposition, [status(thm), theory('equality')], [c_27910, c_38136])).
% 23.01/12.00  tff(c_38878, plain, (![D_3679, A_3680]: (v5_pre_topc(D_3679, A_3680, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_3679, A_3680, '#skF_2') | ~m1_subset_1(D_3679, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_3679, u1_struct_0(A_3680), '#skF_4') | ~v1_funct_1(D_3679) | ~l1_pre_topc(A_3680) | ~v2_pre_topc(A_3680))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_27910, c_22515, c_27910, c_37640, c_27910, c_22515, c_37640, c_27910, c_38148])).
% 23.01/12.00  tff(c_37644, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_37640, c_27915])).
% 23.01/12.00  tff(c_33834, plain, (![A_3158]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_3158), u1_pre_topc(A_3158))) | ~l1_pre_topc(A_3158) | ~v2_pre_topc(A_3158))), inference(cnfTransformation, [status(thm)], [f_178])).
% 23.01/12.00  tff(c_33837, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27910, c_33834])).
% 23.01/12.00  tff(c_33839, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_33837])).
% 23.01/12.00  tff(c_27921, plain, (![A_2622]: (m1_subset_1(u1_pre_topc(A_2622), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2622)))) | ~l1_pre_topc(A_2622))), inference(cnfTransformation, [status(thm)], [f_170])).
% 23.01/12.00  tff(c_27933, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27910, c_27921])).
% 23.01/12.00  tff(c_27938, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_27933])).
% 23.01/12.00  tff(c_27976, plain, (![A_2627, B_2628]: (l1_pre_topc(g1_pre_topc(A_2627, B_2628)) | ~m1_subset_1(B_2628, k1_zfmisc_1(k1_zfmisc_1(A_2627))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/12.00  tff(c_27991, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_27938, c_27976])).
% 23.01/12.00  tff(c_38195, plain, (![D_3583, A_3584, B_3585]: (v5_pre_topc(D_3583, g1_pre_topc(u1_struct_0(A_3584), u1_pre_topc(A_3584)), B_3585) | ~v5_pre_topc(D_3583, A_3584, B_3585) | ~m1_subset_1(D_3583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3584), u1_pre_topc(A_3584))), u1_struct_0(B_3585)))) | ~v1_funct_2(D_3583, u1_struct_0(g1_pre_topc(u1_struct_0(A_3584), u1_pre_topc(A_3584))), u1_struct_0(B_3585)) | ~m1_subset_1(D_3583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3584), u1_struct_0(B_3585)))) | ~v1_funct_2(D_3583, u1_struct_0(A_3584), u1_struct_0(B_3585)) | ~v1_funct_1(D_3583) | ~l1_pre_topc(B_3585) | ~v2_pre_topc(B_3585) | ~l1_pre_topc(A_3584) | ~v2_pre_topc(A_3584))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_38201, plain, (![D_3583, A_3584]: (v5_pre_topc(D_3583, g1_pre_topc(u1_struct_0(A_3584), u1_pre_topc(A_3584)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_3583, A_3584, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_3583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3584), u1_pre_topc(A_3584))), '#skF_4'))) | ~v1_funct_2(D_3583, u1_struct_0(g1_pre_topc(u1_struct_0(A_3584), u1_pre_topc(A_3584))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_3583, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3584), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_3583, u1_struct_0(A_3584), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))) | ~v1_funct_1(D_3583) | ~l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_3584) | ~v2_pre_topc(A_3584))), inference(superposition, [status(thm), theory('equality')], [c_37640, c_38195])).
% 23.01/12.00  tff(c_38265, plain, (![D_3589, A_3590]: (v5_pre_topc(D_3589, g1_pre_topc(u1_struct_0(A_3590), u1_pre_topc(A_3590)), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_3589, A_3590, g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2(D_3589, u1_struct_0(g1_pre_topc(u1_struct_0(A_3590), u1_pre_topc(A_3590))), '#skF_4') | ~m1_subset_1(D_3589, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_3589, u1_struct_0(A_3590), '#skF_4') | ~v1_funct_1(D_3589) | ~l1_pre_topc(A_3590) | ~v2_pre_topc(A_3590))), inference(demodulation, [status(thm), theory('equality')], [c_33839, c_27991, c_37640, c_22515, c_37640, c_37640, c_22515, c_38201])).
% 23.01/12.00  tff(c_33767, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_27910, c_18960])).
% 23.01/12.00  tff(c_38268, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38265, c_33767])).
% 23.01/12.00  tff(c_38277, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_27914, c_22513, c_37644, c_38268])).
% 23.01/12.00  tff(c_38900, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38878, c_38277])).
% 23.01/12.00  tff(c_38918, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_27914, c_22513, c_18959, c_38900])).
% 23.01/12.00  tff(c_38920, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(splitRight, [status(thm)], [c_37569])).
% 23.01/12.00  tff(c_39239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39184, c_38920])).
% 23.01/12.00  tff(c_39241, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_39042])).
% 23.01/12.00  tff(c_39340, plain, (![B_3691]: (v1_funct_2('#skF_4', '#skF_4', B_3691))), inference(demodulation, [status(thm), theory('equality')], [c_39241, c_39025])).
% 23.01/12.00  tff(c_38919, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_37569])).
% 23.01/12.00  tff(c_27959, plain, (![C_2624, A_2625, B_2626]: (v4_relat_1(C_2624, A_2625) | ~m1_subset_1(C_2624, k1_zfmisc_1(k2_zfmisc_1(A_2625, B_2626))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/12.00  tff(c_27974, plain, (![A_2625]: (v4_relat_1('#skF_4', A_2625))), inference(resolution, [status(thm)], [c_22513, c_27959])).
% 23.01/12.00  tff(c_33857, plain, (![B_3168, A_3169]: (k1_relat_1(B_3168)=A_3169 | ~v1_partfun1(B_3168, A_3169) | ~v4_relat_1(B_3168, A_3169) | ~v1_relat_1(B_3168))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_33860, plain, (![A_2625]: (k1_relat_1('#skF_4')=A_2625 | ~v1_partfun1('#skF_4', A_2625) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_27974, c_33857])).
% 23.01/12.00  tff(c_33863, plain, (![A_2625]: (k1_relat_1('#skF_4')=A_2625 | ~v1_partfun1('#skF_4', A_2625))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_33860])).
% 23.01/12.00  tff(c_38924, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_38919, c_33863])).
% 23.01/12.00  tff(c_39269, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_39241, c_38924])).
% 23.01/12.00  tff(c_39556, plain, (![D_3730, A_3731, B_3732]: (v5_pre_topc(D_3730, g1_pre_topc(u1_struct_0(A_3731), u1_pre_topc(A_3731)), B_3732) | ~v5_pre_topc(D_3730, A_3731, B_3732) | ~m1_subset_1(D_3730, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3731), u1_pre_topc(A_3731))), u1_struct_0(B_3732)))) | ~v1_funct_2(D_3730, u1_struct_0(g1_pre_topc(u1_struct_0(A_3731), u1_pre_topc(A_3731))), u1_struct_0(B_3732)) | ~m1_subset_1(D_3730, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3731), u1_struct_0(B_3732)))) | ~v1_funct_2(D_3730, u1_struct_0(A_3731), u1_struct_0(B_3732)) | ~v1_funct_1(D_3730) | ~l1_pre_topc(B_3732) | ~v2_pre_topc(B_3732) | ~l1_pre_topc(A_3731) | ~v2_pre_topc(A_3731))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_39575, plain, (![A_3731, B_3732]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_3731), u1_pre_topc(A_3731)), B_3732) | ~v5_pre_topc('#skF_4', A_3731, B_3732) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_3731), u1_pre_topc(A_3731))), u1_struct_0(B_3732)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3731), u1_struct_0(B_3732)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_3731), u1_struct_0(B_3732)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_3732) | ~v2_pre_topc(B_3732) | ~l1_pre_topc(A_3731) | ~v2_pre_topc(A_3731))), inference(resolution, [status(thm)], [c_22513, c_39556])).
% 23.01/12.00  tff(c_40167, plain, (![A_3812, B_3813]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_3812), u1_pre_topc(A_3812)), B_3813) | ~v5_pre_topc('#skF_4', A_3812, B_3813) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_3812), u1_pre_topc(A_3812))), u1_struct_0(B_3813)) | ~v1_funct_2('#skF_4', u1_struct_0(A_3812), u1_struct_0(B_3813)) | ~l1_pre_topc(B_3813) | ~v2_pre_topc(B_3813) | ~l1_pre_topc(A_3812) | ~v2_pre_topc(A_3812))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_39575])).
% 23.01/12.00  tff(c_40179, plain, (![B_3813]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3813) | ~v5_pre_topc('#skF_4', '#skF_1', B_3813) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_3813)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_3813)) | ~l1_pre_topc(B_3813) | ~v2_pre_topc(B_3813) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_39269, c_40167])).
% 23.01/12.00  tff(c_40195, plain, (![B_3813]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3813) | ~v5_pre_topc('#skF_4', '#skF_1', B_3813) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_3813)) | ~l1_pre_topc(B_3813) | ~v2_pre_topc(B_3813))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_39340, c_40179])).
% 23.01/12.00  tff(c_27992, plain, (![A_45]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_45), u1_pre_topc(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_27976])).
% 23.01/12.00  tff(c_38966, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_38924, c_27992])).
% 23.01/12.00  tff(c_38993, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_38966])).
% 23.01/12.00  tff(c_38996, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_27992, c_38993])).
% 23.01/12.00  tff(c_39000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_38996])).
% 23.01/12.00  tff(c_39002, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_38966])).
% 23.01/12.00  tff(c_39302, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_39269, c_66])).
% 23.01/12.00  tff(c_39324, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_39002, c_39302])).
% 23.01/12.00  tff(c_39766, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_39324])).
% 23.01/12.00  tff(c_39769, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_39766])).
% 23.01/12.00  tff(c_39773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_39769])).
% 23.01/12.00  tff(c_39775, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_39324])).
% 23.01/12.00  tff(c_39482, plain, (![D_3723, A_3724, B_3725]: (v5_pre_topc(D_3723, A_3724, g1_pre_topc(u1_struct_0(B_3725), u1_pre_topc(B_3725))) | ~v5_pre_topc(D_3723, A_3724, B_3725) | ~m1_subset_1(D_3723, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3724), u1_struct_0(g1_pre_topc(u1_struct_0(B_3725), u1_pre_topc(B_3725)))))) | ~v1_funct_2(D_3723, u1_struct_0(A_3724), u1_struct_0(g1_pre_topc(u1_struct_0(B_3725), u1_pre_topc(B_3725)))) | ~m1_subset_1(D_3723, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3724), u1_struct_0(B_3725)))) | ~v1_funct_2(D_3723, u1_struct_0(A_3724), u1_struct_0(B_3725)) | ~v1_funct_1(D_3723) | ~l1_pre_topc(B_3725) | ~v2_pre_topc(B_3725) | ~l1_pre_topc(A_3724) | ~v2_pre_topc(A_3724))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_39501, plain, (![A_3724, B_3725]: (v5_pre_topc('#skF_4', A_3724, g1_pre_topc(u1_struct_0(B_3725), u1_pre_topc(B_3725))) | ~v5_pre_topc('#skF_4', A_3724, B_3725) | ~v1_funct_2('#skF_4', u1_struct_0(A_3724), u1_struct_0(g1_pre_topc(u1_struct_0(B_3725), u1_pre_topc(B_3725)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3724), u1_struct_0(B_3725)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_3724), u1_struct_0(B_3725)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_3725) | ~v2_pre_topc(B_3725) | ~l1_pre_topc(A_3724) | ~v2_pre_topc(A_3724))), inference(resolution, [status(thm)], [c_22513, c_39482])).
% 23.01/12.00  tff(c_40270, plain, (![A_3820, B_3821]: (v5_pre_topc('#skF_4', A_3820, g1_pre_topc(u1_struct_0(B_3821), u1_pre_topc(B_3821))) | ~v5_pre_topc('#skF_4', A_3820, B_3821) | ~v1_funct_2('#skF_4', u1_struct_0(A_3820), u1_struct_0(g1_pre_topc(u1_struct_0(B_3821), u1_pre_topc(B_3821)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_3820), u1_struct_0(B_3821)) | ~l1_pre_topc(B_3821) | ~v2_pre_topc(B_3821) | ~l1_pre_topc(A_3820) | ~v2_pre_topc(A_3820))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22513, c_39501])).
% 23.01/12.00  tff(c_40279, plain, (![B_3821]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_3821), u1_pre_topc(B_3821))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3821) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_3821), u1_pre_topc(B_3821)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_3821)) | ~l1_pre_topc(B_3821) | ~v2_pre_topc(B_3821) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_39269, c_40270])).
% 23.01/12.00  tff(c_40329, plain, (![B_3823]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_3823), u1_pre_topc(B_3823))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_3823) | ~l1_pre_topc(B_3823) | ~v2_pre_topc(B_3823))), inference(demodulation, [status(thm), theory('equality')], [c_39775, c_39002, c_39340, c_39269, c_39340, c_40279])).
% 23.01/12.00  tff(c_40341, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27910, c_40329])).
% 23.01/12.00  tff(c_40348, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_40341])).
% 23.01/12.00  tff(c_40349, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_33767, c_40348])).
% 23.01/12.00  tff(c_40352, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40195, c_40349])).
% 23.01/12.00  tff(c_40356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_27914, c_27910, c_18959, c_40352])).
% 23.01/12.00  tff(c_40358, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_239])).
% 23.01/12.00  tff(c_40375, plain, (k1_zfmisc_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40358, c_144])).
% 23.01/12.00  tff(c_44107, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44094, c_44094, c_40375])).
% 23.01/12.00  tff(c_44112, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44094, c_44094, c_10])).
% 23.01/12.00  tff(c_44111, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_44094, c_20])).
% 23.01/12.00  tff(c_44469, plain, (![A_4255, B_4256, C_4257]: (k1_relset_1(A_4255, B_4256, C_4257)=k1_relat_1(C_4257) | ~m1_subset_1(C_4257, k1_zfmisc_1(k2_zfmisc_1(A_4255, B_4256))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_44484, plain, (![A_4255, B_4256]: (k1_relset_1(A_4255, B_4256, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_44111, c_44469])).
% 23.01/12.00  tff(c_44594, plain, (![C_4284, A_4285, B_4286]: (v1_funct_2(C_4284, A_4285, B_4286) | k1_relset_1(A_4285, B_4286, C_4284)!=A_4285 | ~m1_subset_1(C_4284, k1_zfmisc_1(k2_zfmisc_1(A_4285, B_4286))) | ~v1_funct_1(C_4284))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_44598, plain, (![A_4285, B_4286]: (v1_funct_2('#skF_4', A_4285, B_4286) | k1_relset_1(A_4285, B_4286, '#skF_4')!=A_4285 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_44111, c_44594])).
% 23.01/12.00  tff(c_44611, plain, (![A_4285, B_4286]: (v1_funct_2('#skF_4', A_4285, B_4286) | k1_relat_1('#skF_4')!=A_4285)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_44484, c_44598])).
% 23.01/12.00  tff(c_45465, plain, (![C_4326, A_4327, B_4328]: (~v1_xboole_0(C_4326) | ~v1_funct_2(C_4326, A_4327, B_4328) | ~v1_funct_1(C_4326) | ~m1_subset_1(C_4326, k1_zfmisc_1(k2_zfmisc_1(A_4327, B_4328))) | v1_xboole_0(B_4328) | v1_xboole_0(A_4327))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_45469, plain, (![A_4327, B_4328]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_4327, B_4328) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_4328) | v1_xboole_0(A_4327))), inference(resolution, [status(thm)], [c_44111, c_45465])).
% 23.01/12.00  tff(c_45572, plain, (![A_4334, B_4335]: (~v1_funct_2('#skF_4', A_4334, B_4335) | v1_xboole_0(B_4335) | v1_xboole_0(A_4334))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_44082, c_45469])).
% 23.01/12.00  tff(c_45581, plain, (![B_4286, A_4285]: (v1_xboole_0(B_4286) | v1_xboole_0(A_4285) | k1_relat_1('#skF_4')!=A_4285)), inference(resolution, [status(thm)], [c_44611, c_45572])).
% 23.01/12.00  tff(c_45585, plain, (![A_4336]: (v1_xboole_0(A_4336) | k1_relat_1('#skF_4')!=A_4336)), inference(splitLeft, [status(thm)], [c_45581])).
% 23.01/12.00  tff(c_44095, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_44082, c_4])).
% 23.01/12.00  tff(c_45633, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_45585, c_44095])).
% 23.01/12.00  tff(c_44647, plain, (![C_4294, A_4295, B_4296]: (v1_partfun1(C_4294, A_4295) | ~v1_funct_2(C_4294, A_4295, B_4296) | ~v1_funct_1(C_4294) | ~m1_subset_1(C_4294, k1_zfmisc_1(k2_zfmisc_1(A_4295, B_4296))) | v1_xboole_0(B_4296))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_44651, plain, (![A_4295, B_4296]: (v1_partfun1('#skF_4', A_4295) | ~v1_funct_2('#skF_4', A_4295, B_4296) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_4296))), inference(resolution, [status(thm)], [c_44111, c_44647])).
% 23.01/12.00  tff(c_44668, plain, (![A_4297, B_4298]: (v1_partfun1('#skF_4', A_4297) | ~v1_funct_2('#skF_4', A_4297, B_4298) | v1_xboole_0(B_4298))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_44651])).
% 23.01/12.00  tff(c_44677, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_44668])).
% 23.01/12.00  tff(c_44683, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40561, c_44677])).
% 23.01/12.00  tff(c_44113, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44094, c_44094, c_8])).
% 23.01/12.00  tff(c_44436, plain, (![B_4247, A_4248, B_4249]: (v4_relat_1(B_4247, A_4248) | ~v1_xboole_0(B_4247) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(A_4248, B_4249))))), inference(resolution, [status(thm)], [c_16, c_40504])).
% 23.01/12.00  tff(c_44438, plain, (![B_4247, A_3]: (v4_relat_1(B_4247, A_3) | ~v1_xboole_0(B_4247) | ~v1_xboole_0(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_44113, c_44436])).
% 23.01/12.00  tff(c_44445, plain, (![B_4250, A_4251]: (v4_relat_1(B_4250, A_4251) | ~v1_xboole_0(B_4250))), inference(demodulation, [status(thm), theory('equality')], [c_44082, c_44107, c_44438])).
% 23.01/12.00  tff(c_48, plain, (![B_36, A_35]: (k1_relat_1(B_36)=A_35 | ~v1_partfun1(B_36, A_35) | ~v4_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_44453, plain, (![B_4250, A_4251]: (k1_relat_1(B_4250)=A_4251 | ~v1_partfun1(B_4250, A_4251) | ~v1_relat_1(B_4250) | ~v1_xboole_0(B_4250))), inference(resolution, [status(thm)], [c_44445, c_48])).
% 23.01/12.00  tff(c_44686, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_44683, c_44453])).
% 23.01/12.00  tff(c_44692, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44082, c_220, c_44686])).
% 23.01/12.00  tff(c_18, plain, (![B_6, A_5]: (v1_xboole_0(B_6) | ~m1_subset_1(B_6, A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.01/12.00  tff(c_180, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(resolution, [status(thm)], [c_111, c_18])).
% 23.01/12.00  tff(c_40564, plain, (~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_180])).
% 23.01/12.00  tff(c_44696, plain, (~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_44692, c_40564])).
% 23.01/12.00  tff(c_45643, plain, (~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_45633, c_44696])).
% 23.01/12.00  tff(c_45655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44082, c_44107, c_44112, c_45643])).
% 23.01/12.00  tff(c_45656, plain, (![B_4286]: (v1_xboole_0(B_4286))), inference(splitRight, [status(thm)], [c_45581])).
% 23.01/12.00  tff(c_45719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45656, c_44696])).
% 23.01/12.00  tff(c_45720, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_180])).
% 23.01/12.00  tff(c_45732, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_45720, c_144])).
% 23.01/12.00  tff(c_45750, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45732, c_45732, c_10])).
% 23.01/12.00  tff(c_45749, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_45732, c_20])).
% 23.01/12.00  tff(c_46057, plain, (![A_4371, B_4372, C_4373]: (k1_relset_1(A_4371, B_4372, C_4373)=k1_relat_1(C_4373) | ~m1_subset_1(C_4373, k1_zfmisc_1(k2_zfmisc_1(A_4371, B_4372))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_46075, plain, (![A_4371, B_4372]: (k1_relset_1(A_4371, B_4372, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_45749, c_46057])).
% 23.01/12.00  tff(c_46292, plain, (![C_4409, A_4410, B_4411]: (v1_funct_2(C_4409, A_4410, B_4411) | k1_relset_1(A_4410, B_4411, C_4409)!=A_4410 | ~m1_subset_1(C_4409, k1_zfmisc_1(k2_zfmisc_1(A_4410, B_4411))) | ~v1_funct_1(C_4409))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_46296, plain, (![A_4410, B_4411]: (v1_funct_2('#skF_4', A_4410, B_4411) | k1_relset_1(A_4410, B_4411, '#skF_4')!=A_4410 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_45749, c_46292])).
% 23.01/12.00  tff(c_46309, plain, (![A_4410, B_4411]: (v1_funct_2('#skF_4', A_4410, B_4411) | k1_relat_1('#skF_4')!=A_4410)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46075, c_46296])).
% 23.01/12.00  tff(c_47160, plain, (![C_4445, A_4446, B_4447]: (~v1_xboole_0(C_4445) | ~v1_funct_2(C_4445, A_4446, B_4447) | ~v1_funct_1(C_4445) | ~m1_subset_1(C_4445, k1_zfmisc_1(k2_zfmisc_1(A_4446, B_4447))) | v1_xboole_0(B_4447) | v1_xboole_0(A_4446))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_47167, plain, (![A_4446, B_4447]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_4446, B_4447) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_4447) | v1_xboole_0(A_4446))), inference(resolution, [status(thm)], [c_45749, c_47160])).
% 23.01/12.00  tff(c_47192, plain, (![A_4449, B_4450]: (~v1_funct_2('#skF_4', A_4449, B_4450) | v1_xboole_0(B_4450) | v1_xboole_0(A_4449))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_45720, c_47167])).
% 23.01/12.00  tff(c_47196, plain, (![B_4411, A_4410]: (v1_xboole_0(B_4411) | v1_xboole_0(A_4410) | k1_relat_1('#skF_4')!=A_4410)), inference(resolution, [status(thm)], [c_46309, c_47192])).
% 23.01/12.00  tff(c_47209, plain, (![A_4451]: (v1_xboole_0(A_4451) | k1_relat_1('#skF_4')!=A_4451)), inference(splitLeft, [status(thm)], [c_47196])).
% 23.01/12.00  tff(c_45733, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_45720, c_4])).
% 23.01/12.00  tff(c_47245, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_47209, c_45733])).
% 23.01/12.00  tff(c_40388, plain, (m1_subset_1(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40375, c_20])).
% 23.01/12.00  tff(c_45744, plain, (m1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_45732, c_45732, c_40388])).
% 23.01/12.00  tff(c_46315, plain, (![A_4412, B_4413]: (v1_funct_2('#skF_4', A_4412, B_4413) | k1_relat_1('#skF_4')!=A_4412)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46075, c_46296])).
% 23.01/12.00  tff(c_45745, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_45732, c_45732, c_40375])).
% 23.01/12.00  tff(c_46164, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, '#skF_4') | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_45745, c_45732, c_45732, c_45732, c_113])).
% 23.01/12.00  tff(c_46322, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_46315, c_46164])).
% 23.01/12.00  tff(c_46326, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_45744, c_46322])).
% 23.01/12.00  tff(c_46327, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_46326])).
% 23.01/12.00  tff(c_47264, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47245, c_46327])).
% 23.01/12.00  tff(c_47265, plain, (![B_4411]: (v1_xboole_0(B_4411))), inference(splitRight, [status(thm)], [c_47196])).
% 23.01/12.00  tff(c_46204, plain, (![C_4404, A_4405, B_4406]: (v1_partfun1(C_4404, A_4405) | ~v1_funct_2(C_4404, A_4405, B_4406) | ~v1_funct_1(C_4404) | ~m1_subset_1(C_4404, k1_zfmisc_1(k2_zfmisc_1(A_4405, B_4406))) | v1_xboole_0(B_4406))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_46211, plain, (![A_4405, B_4406]: (v1_partfun1('#skF_4', A_4405) | ~v1_funct_2('#skF_4', A_4405, B_4406) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_4406))), inference(resolution, [status(thm)], [c_45749, c_46204])).
% 23.01/12.00  tff(c_46229, plain, (![A_4407, B_4408]: (v1_partfun1('#skF_4', A_4407) | ~v1_funct_2('#skF_4', A_4407, B_4408) | v1_xboole_0(B_4408))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_46211])).
% 23.01/12.00  tff(c_46232, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_46229])).
% 23.01/12.00  tff(c_46238, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40561, c_46232])).
% 23.01/12.00  tff(c_40528, plain, (![A_3845]: (v4_relat_1(k1_xboole_0, A_3845))), inference(resolution, [status(thm)], [c_20, c_40504])).
% 23.01/12.00  tff(c_45735, plain, (![A_3845]: (v4_relat_1('#skF_4', A_3845))), inference(demodulation, [status(thm), theory('equality')], [c_45732, c_40528])).
% 23.01/12.00  tff(c_46012, plain, (![B_4361, A_4362]: (k1_relat_1(B_4361)=A_4362 | ~v1_partfun1(B_4361, A_4362) | ~v4_relat_1(B_4361, A_4362) | ~v1_relat_1(B_4361))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_46018, plain, (![A_3845]: (k1_relat_1('#skF_4')=A_3845 | ~v1_partfun1('#skF_4', A_3845) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_45735, c_46012])).
% 23.01/12.00  tff(c_46022, plain, (![A_3845]: (k1_relat_1('#skF_4')=A_3845 | ~v1_partfun1('#skF_4', A_3845))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_46018])).
% 23.01/12.00  tff(c_46243, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_46238, c_46022])).
% 23.01/12.00  tff(c_40450, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_46248, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46243, c_40450])).
% 23.01/12.00  tff(c_47311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47265, c_46248])).
% 23.01/12.00  tff(c_47313, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_46326])).
% 23.01/12.00  tff(c_47345, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47313, c_46248])).
% 23.01/12.00  tff(c_47353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_45720, c_45750, c_47345])).
% 23.01/12.00  tff(c_47354, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_40554])).
% 23.01/12.00  tff(c_47366, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_47354, c_144])).
% 23.01/12.00  tff(c_47384, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47366, c_47366, c_8])).
% 23.01/12.00  tff(c_47355, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_40554])).
% 23.01/12.00  tff(c_47438, plain, (![A_4460]: (A_4460='#skF_4' | ~v1_xboole_0(A_4460))), inference(resolution, [status(thm)], [c_47354, c_4])).
% 23.01/12.00  tff(c_47445, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_47355, c_47438])).
% 23.01/12.00  tff(c_47450, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_47445, c_40450])).
% 23.01/12.00  tff(c_47663, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_47354, c_47384, c_47450])).
% 23.01/12.00  tff(c_47664, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_47676, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_47664, c_144])).
% 23.01/12.00  tff(c_47682, plain, (m1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_47676, c_40388])).
% 23.01/12.00  tff(c_47665, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_47677, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_47664, c_4])).
% 23.01/12.00  tff(c_47855, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_47665, c_47677])).
% 23.01/12.00  tff(c_47925, plain, (![B_4499, A_4500]: (B_4499='#skF_4' | A_4500='#skF_4' | k2_zfmisc_1(A_4500, B_4499)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_47676, c_47676, c_6])).
% 23.01/12.00  tff(c_47935, plain, (u1_struct_0('#skF_2')='#skF_4' | u1_struct_0('#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_47855, c_47925])).
% 23.01/12.00  tff(c_47940, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitLeft, [status(thm)], [c_47935])).
% 23.01/12.00  tff(c_47943, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_47940, c_107])).
% 23.01/12.00  tff(c_47683, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_47676, c_40375])).
% 23.01/12.00  tff(c_48193, plain, (![C_4535, B_4536]: (v1_partfun1(C_4535, '#skF_4') | ~v1_funct_2(C_4535, '#skF_4', B_4536) | ~m1_subset_1(C_4535, '#skF_4') | ~v1_funct_1(C_4535))), inference(demodulation, [status(thm), theory('equality')], [c_47683, c_47676, c_47676, c_47676, c_113])).
% 23.01/12.00  tff(c_48196, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_47943, c_48193])).
% 23.01/12.00  tff(c_48199, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47682, c_48196])).
% 23.01/12.00  tff(c_47687, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_20])).
% 23.01/12.00  tff(c_47858, plain, (![C_4482, A_4483, B_4484]: (v4_relat_1(C_4482, A_4483) | ~m1_subset_1(C_4482, k1_zfmisc_1(k2_zfmisc_1(A_4483, B_4484))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/12.00  tff(c_47873, plain, (![A_4483]: (v4_relat_1('#skF_4', A_4483))), inference(resolution, [status(thm)], [c_47687, c_47858])).
% 23.01/12.00  tff(c_48096, plain, (![B_4517, A_4518]: (k1_relat_1(B_4517)=A_4518 | ~v1_partfun1(B_4517, A_4518) | ~v4_relat_1(B_4517, A_4518) | ~v1_relat_1(B_4517))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_48102, plain, (![A_4483]: (k1_relat_1('#skF_4')=A_4483 | ~v1_partfun1('#skF_4', A_4483) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_47873, c_48096])).
% 23.01/12.00  tff(c_48106, plain, (![A_4483]: (k1_relat_1('#skF_4')=A_4483 | ~v1_partfun1('#skF_4', A_4483))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_48102])).
% 23.01/12.00  tff(c_48203, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_48199, c_48106])).
% 23.01/12.00  tff(c_48131, plain, (![A_4524, B_4525, C_4526]: (k1_relset_1(A_4524, B_4525, C_4526)=k1_relat_1(C_4526) | ~m1_subset_1(C_4526, k1_zfmisc_1(k2_zfmisc_1(A_4524, B_4525))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_48146, plain, (![A_4524, B_4525]: (k1_relset_1(A_4524, B_4525, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_48131])).
% 23.01/12.00  tff(c_48204, plain, (![A_4524, B_4525]: (k1_relset_1(A_4524, B_4525, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48203, c_48146])).
% 23.01/12.00  tff(c_49578, plain, (![C_4681, A_4682, B_4683]: (v1_funct_2(C_4681, A_4682, B_4683) | k1_relset_1(A_4682, B_4683, C_4681)!=A_4682 | ~m1_subset_1(C_4681, k1_zfmisc_1(k2_zfmisc_1(A_4682, B_4683))) | ~v1_funct_1(C_4681))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_49582, plain, (![A_4682, B_4683]: (v1_funct_2('#skF_4', A_4682, B_4683) | k1_relset_1(A_4682, B_4683, '#skF_4')!=A_4682 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_49578])).
% 23.01/12.00  tff(c_49599, plain, (![B_4683]: (v1_funct_2('#skF_4', '#skF_4', B_4683))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48204, c_49582])).
% 23.01/12.00  tff(c_48411, plain, (![C_4560, A_4561, B_4562]: (v1_funct_2(C_4560, A_4561, B_4562) | k1_relset_1(A_4561, B_4562, C_4560)!=A_4561 | ~m1_subset_1(C_4560, k1_zfmisc_1(k2_zfmisc_1(A_4561, B_4562))) | ~v1_funct_1(C_4560))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_48415, plain, (![A_4561, B_4562]: (v1_funct_2('#skF_4', A_4561, B_4562) | k1_relset_1(A_4561, B_4562, '#skF_4')!=A_4561 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_48411])).
% 23.01/12.00  tff(c_48459, plain, (![B_4562]: (v1_funct_2('#skF_4', '#skF_4', B_4562))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48204, c_48415])).
% 23.01/12.00  tff(c_47955, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47940, c_64])).
% 23.01/12.00  tff(c_47963, plain, (m1_subset_1(u1_pre_topc('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_47683, c_47683, c_47955])).
% 23.01/12.00  tff(c_40386, plain, (![B_10]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_xboole_0) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40375, c_22])).
% 23.01/12.00  tff(c_40393, plain, (![B_10]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_40386])).
% 23.01/12.00  tff(c_47679, plain, (![B_10]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_40393])).
% 23.01/12.00  tff(c_47974, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_47963, c_47679])).
% 23.01/12.00  tff(c_47987, plain, (u1_pre_topc('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_47974, c_47677])).
% 23.01/12.00  tff(c_47740, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40401, c_108])).
% 23.01/12.00  tff(c_47942, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47940, c_47740])).
% 23.01/12.00  tff(c_48079, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_47987, c_47942])).
% 23.01/12.00  tff(c_48054, plain, (![A_4507]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_4507), u1_pre_topc(A_4507))) | ~l1_pre_topc(A_4507) | ~v2_pre_topc(A_4507))), inference(cnfTransformation, [status(thm)], [f_178])).
% 23.01/12.00  tff(c_48060, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_47940, c_48054])).
% 23.01/12.00  tff(c_48064, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_47987, c_48060])).
% 23.01/12.00  tff(c_40359, plain, (![A_3824, B_3825]: (l1_pre_topc(g1_pre_topc(A_3824, B_3825)) | ~m1_subset_1(B_3825, k1_zfmisc_1(k1_zfmisc_1(A_3824))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/12.00  tff(c_40369, plain, (![A_3824]: (l1_pre_topc(g1_pre_topc(A_3824, k1_xboole_0)))), inference(resolution, [status(thm)], [c_20, c_40359])).
% 23.01/12.00  tff(c_47681, plain, (![A_3824]: (l1_pre_topc(g1_pre_topc(A_3824, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_40369])).
% 23.01/12.00  tff(c_47944, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_47940, c_82])).
% 23.01/12.00  tff(c_47992, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_47987, c_47944])).
% 23.01/12.00  tff(c_48307, plain, (![B_4551, C_4552, A_4553]: (B_4551='#skF_4' | v1_partfun1(C_4552, A_4553) | ~v1_funct_2(C_4552, A_4553, B_4551) | ~m1_subset_1(C_4552, k1_zfmisc_1(k2_zfmisc_1(A_4553, B_4551))) | ~v1_funct_1(C_4552))), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_58])).
% 23.01/12.00  tff(c_48311, plain, (![B_4551, A_4553]: (B_4551='#skF_4' | v1_partfun1('#skF_4', A_4553) | ~v1_funct_2('#skF_4', A_4553, B_4551) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_48307])).
% 23.01/12.00  tff(c_48329, plain, (![B_4554, A_4555]: (B_4554='#skF_4' | v1_partfun1('#skF_4', A_4555) | ~v1_funct_2('#skF_4', A_4555, B_4554))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48311])).
% 23.01/12.00  tff(c_48336, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_47992, c_48329])).
% 23.01/12.00  tff(c_48350, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_48336])).
% 23.01/12.00  tff(c_48205, plain, (![A_4483]: (A_4483='#skF_4' | ~v1_partfun1('#skF_4', A_4483))), inference(demodulation, [status(thm), theory('equality')], [c_48203, c_48106])).
% 23.01/12.00  tff(c_48355, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_48350, c_48205])).
% 23.01/12.00  tff(c_47688, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_47676, c_10])).
% 23.01/12.00  tff(c_48563, plain, (![D_4575, A_4576, B_4577]: (v5_pre_topc(D_4575, A_4576, B_4577) | ~v5_pre_topc(D_4575, A_4576, g1_pre_topc(u1_struct_0(B_4577), u1_pre_topc(B_4577))) | ~m1_subset_1(D_4575, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4576), u1_struct_0(g1_pre_topc(u1_struct_0(B_4577), u1_pre_topc(B_4577)))))) | ~v1_funct_2(D_4575, u1_struct_0(A_4576), u1_struct_0(g1_pre_topc(u1_struct_0(B_4577), u1_pre_topc(B_4577)))) | ~m1_subset_1(D_4575, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4576), u1_struct_0(B_4577)))) | ~v1_funct_2(D_4575, u1_struct_0(A_4576), u1_struct_0(B_4577)) | ~v1_funct_1(D_4575) | ~l1_pre_topc(B_4577) | ~v2_pre_topc(B_4577) | ~l1_pre_topc(A_4576) | ~v2_pre_topc(A_4576))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_48569, plain, (![D_4575, B_4577]: (v5_pre_topc(D_4575, g1_pre_topc('#skF_4', '#skF_4'), B_4577) | ~v5_pre_topc(D_4575, g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0(B_4577), u1_pre_topc(B_4577))) | ~m1_subset_1(D_4575, k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_4577), u1_pre_topc(B_4577)))))) | ~v1_funct_2(D_4575, u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(g1_pre_topc(u1_struct_0(B_4577), u1_pre_topc(B_4577)))) | ~m1_subset_1(D_4575, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(B_4577)))) | ~v1_funct_2(D_4575, u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(B_4577)) | ~v1_funct_1(D_4575) | ~l1_pre_topc(B_4577) | ~v2_pre_topc(B_4577) | ~l1_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_48355, c_48563])).
% 23.01/12.00  tff(c_49494, plain, (![D_4678, B_4679]: (v5_pre_topc(D_4678, g1_pre_topc('#skF_4', '#skF_4'), B_4679) | ~v5_pre_topc(D_4678, g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0(B_4679), u1_pre_topc(B_4679))) | ~v1_funct_2(D_4678, '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_4679), u1_pre_topc(B_4679)))) | ~m1_subset_1(D_4678, '#skF_4') | ~v1_funct_2(D_4678, '#skF_4', u1_struct_0(B_4679)) | ~v1_funct_1(D_4678) | ~l1_pre_topc(B_4679) | ~v2_pre_topc(B_4679))), inference(demodulation, [status(thm), theory('equality')], [c_48064, c_47681, c_48355, c_47683, c_47688, c_48355, c_48355, c_47683, c_47688, c_48569])).
% 23.01/12.00  tff(c_49507, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48079, c_49494])).
% 23.01/12.00  tff(c_49521, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_48459, c_47682, c_48459, c_49507])).
% 23.01/12.00  tff(c_48736, plain, (![D_4591, A_4592, B_4593]: (v5_pre_topc(D_4591, A_4592, B_4593) | ~v5_pre_topc(D_4591, g1_pre_topc(u1_struct_0(A_4592), u1_pre_topc(A_4592)), B_4593) | ~m1_subset_1(D_4591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4592), u1_pre_topc(A_4592))), u1_struct_0(B_4593)))) | ~v1_funct_2(D_4591, u1_struct_0(g1_pre_topc(u1_struct_0(A_4592), u1_pre_topc(A_4592))), u1_struct_0(B_4593)) | ~m1_subset_1(D_4591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4592), u1_struct_0(B_4593)))) | ~v1_funct_2(D_4591, u1_struct_0(A_4592), u1_struct_0(B_4593)) | ~v1_funct_1(D_4591) | ~l1_pre_topc(B_4593) | ~v2_pre_topc(B_4593) | ~l1_pre_topc(A_4592) | ~v2_pre_topc(A_4592))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_48748, plain, (![D_4591, B_4593]: (v5_pre_topc(D_4591, '#skF_1', B_4593) | ~v5_pre_topc(D_4591, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_4593) | ~m1_subset_1(D_4591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), '#skF_4')), u1_struct_0(B_4593)))) | ~v1_funct_2(D_4591, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_4593)) | ~m1_subset_1(D_4591, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_4593)))) | ~v1_funct_2(D_4591, u1_struct_0('#skF_1'), u1_struct_0(B_4593)) | ~v1_funct_1(D_4591) | ~l1_pre_topc(B_4593) | ~v2_pre_topc(B_4593) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_47987, c_48736])).
% 23.01/12.00  tff(c_48770, plain, (![D_4591, B_4593]: (v5_pre_topc(D_4591, '#skF_1', B_4593) | ~v5_pre_topc(D_4591, g1_pre_topc('#skF_4', '#skF_4'), B_4593) | ~m1_subset_1(D_4591, '#skF_4') | ~v1_funct_2(D_4591, '#skF_4', u1_struct_0(B_4593)) | ~v1_funct_1(D_4591) | ~l1_pre_topc(B_4593) | ~v2_pre_topc(B_4593))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_47940, c_47683, c_47688, c_47940, c_48355, c_47987, c_47940, c_47683, c_47688, c_48355, c_47940, c_47987, c_47940, c_48748])).
% 23.01/12.00  tff(c_49528, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_49521, c_48770])).
% 23.01/12.00  tff(c_49531, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_48459, c_47682, c_49528])).
% 23.01/12.00  tff(c_49533, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40401, c_49531])).
% 23.01/12.00  tff(c_49534, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(splitRight, [status(thm)], [c_48336])).
% 23.01/12.00  tff(c_49550, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_49534, c_40433])).
% 23.01/12.00  tff(c_49728, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_49550])).
% 23.01/12.00  tff(c_49739, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40433, c_49728])).
% 23.01/12.00  tff(c_49743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_49739])).
% 23.01/12.00  tff(c_49745, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_49550])).
% 23.01/12.00  tff(c_50048, plain, (![D_4730, A_4731, B_4732]: (v5_pre_topc(D_4730, g1_pre_topc(u1_struct_0(A_4731), u1_pre_topc(A_4731)), B_4732) | ~v5_pre_topc(D_4730, A_4731, B_4732) | ~m1_subset_1(D_4730, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4731), u1_pre_topc(A_4731))), u1_struct_0(B_4732)))) | ~v1_funct_2(D_4730, u1_struct_0(g1_pre_topc(u1_struct_0(A_4731), u1_pre_topc(A_4731))), u1_struct_0(B_4732)) | ~m1_subset_1(D_4730, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4731), u1_struct_0(B_4732)))) | ~v1_funct_2(D_4730, u1_struct_0(A_4731), u1_struct_0(B_4732)) | ~v1_funct_1(D_4730) | ~l1_pre_topc(B_4732) | ~v2_pre_topc(B_4732) | ~l1_pre_topc(A_4731) | ~v2_pre_topc(A_4731))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_50057, plain, (![D_4730, B_4732]: (v5_pre_topc(D_4730, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_4732) | ~v5_pre_topc(D_4730, '#skF_2', B_4732) | ~m1_subset_1(D_4730, k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0(B_4732)))) | ~v1_funct_2(D_4730, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_4732)) | ~m1_subset_1(D_4730, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_4732)))) | ~v1_funct_2(D_4730, u1_struct_0('#skF_2'), u1_struct_0(B_4732)) | ~v1_funct_1(D_4730) | ~l1_pre_topc(B_4732) | ~v2_pre_topc(B_4732) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_49534, c_50048])).
% 23.01/12.00  tff(c_50467, plain, (![D_4777, B_4778]: (v5_pre_topc(D_4777, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_4778) | ~v5_pre_topc(D_4777, '#skF_2', B_4778) | ~m1_subset_1(D_4777, '#skF_4') | ~v1_funct_2(D_4777, '#skF_4', u1_struct_0(B_4778)) | ~m1_subset_1(D_4777, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_4778)))) | ~v1_funct_2(D_4777, u1_struct_0('#skF_2'), u1_struct_0(B_4778)) | ~v1_funct_1(D_4777) | ~l1_pre_topc(B_4778) | ~v2_pre_topc(B_4778))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_49534, c_47683, c_47688, c_50057])).
% 23.01/12.00  tff(c_50477, plain, (![B_4778]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_4778) | ~v5_pre_topc('#skF_4', '#skF_2', B_4778) | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_4778)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_4778)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_4778) | ~v2_pre_topc(B_4778))), inference(resolution, [status(thm)], [c_47687, c_50467])).
% 23.01/12.00  tff(c_50488, plain, (![B_4778]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_4778) | ~v5_pre_topc('#skF_4', '#skF_2', B_4778) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_4778)) | ~l1_pre_topc(B_4778) | ~v2_pre_topc(B_4778))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_49599, c_47682, c_50477])).
% 23.01/12.00  tff(c_49595, plain, (![A_4682, B_4683]: (v1_funct_2('#skF_4', A_4682, B_4683) | A_4682!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48204, c_49582])).
% 23.01/12.00  tff(c_49660, plain, (![C_4693, A_4694, B_4695]: (~v1_xboole_0(C_4693) | ~v1_funct_2(C_4693, A_4694, B_4695) | ~v1_funct_1(C_4693) | ~m1_subset_1(C_4693, k1_zfmisc_1(k2_zfmisc_1(A_4694, B_4695))) | v1_xboole_0(B_4695) | v1_xboole_0(A_4694))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_49664, plain, (![A_4694, B_4695]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_4694, B_4695) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_4695) | v1_xboole_0(A_4694))), inference(resolution, [status(thm)], [c_47687, c_49660])).
% 23.01/12.00  tff(c_49681, plain, (![A_4696, B_4697]: (~v1_funct_2('#skF_4', A_4696, B_4697) | v1_xboole_0(B_4697) | v1_xboole_0(A_4696))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47664, c_49664])).
% 23.01/12.00  tff(c_49688, plain, (![B_4683, A_4682]: (v1_xboole_0(B_4683) | v1_xboole_0(A_4682) | A_4682!='#skF_4')), inference(resolution, [status(thm)], [c_49595, c_49681])).
% 23.01/12.00  tff(c_49692, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_49688])).
% 23.01/12.00  tff(c_47689, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_47676, c_8])).
% 23.01/12.00  tff(c_50181, plain, (![D_4752, A_4753, B_4754]: (v5_pre_topc(D_4752, A_4753, B_4754) | ~v5_pre_topc(D_4752, A_4753, g1_pre_topc(u1_struct_0(B_4754), u1_pre_topc(B_4754))) | ~m1_subset_1(D_4752, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4753), u1_struct_0(g1_pre_topc(u1_struct_0(B_4754), u1_pre_topc(B_4754)))))) | ~v1_funct_2(D_4752, u1_struct_0(A_4753), u1_struct_0(g1_pre_topc(u1_struct_0(B_4754), u1_pre_topc(B_4754)))) | ~m1_subset_1(D_4752, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4753), u1_struct_0(B_4754)))) | ~v1_funct_2(D_4752, u1_struct_0(A_4753), u1_struct_0(B_4754)) | ~v1_funct_1(D_4752) | ~l1_pre_topc(B_4754) | ~v2_pre_topc(B_4754) | ~l1_pre_topc(A_4753) | ~v2_pre_topc(A_4753))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_50607, plain, (![B_4791, A_4792, B_4793]: (v5_pre_topc(B_4791, A_4792, B_4793) | ~v5_pre_topc(B_4791, A_4792, g1_pre_topc(u1_struct_0(B_4793), u1_pre_topc(B_4793))) | ~v1_funct_2(B_4791, u1_struct_0(A_4792), u1_struct_0(g1_pre_topc(u1_struct_0(B_4793), u1_pre_topc(B_4793)))) | ~m1_subset_1(B_4791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792), u1_struct_0(B_4793)))) | ~v1_funct_2(B_4791, u1_struct_0(A_4792), u1_struct_0(B_4793)) | ~v1_funct_1(B_4791) | ~l1_pre_topc(B_4793) | ~v2_pre_topc(B_4793) | ~l1_pre_topc(A_4792) | ~v2_pre_topc(A_4792) | ~v1_xboole_0(B_4791) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792), u1_struct_0(g1_pre_topc(u1_struct_0(B_4793), u1_pre_topc(B_4793)))))))), inference(resolution, [status(thm)], [c_16, c_50181])).
% 23.01/12.00  tff(c_50618, plain, (![B_4791, A_4792]: (v5_pre_topc(B_4791, A_4792, '#skF_2') | ~v5_pre_topc(B_4791, A_4792, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(B_4791, u1_struct_0(A_4792), '#skF_4') | ~m1_subset_1(B_4791, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792), u1_struct_0('#skF_2')))) | ~v1_funct_2(B_4791, u1_struct_0(A_4792), u1_struct_0('#skF_2')) | ~v1_funct_1(B_4791) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_4792) | ~v2_pre_topc(A_4792) | ~v1_xboole_0(B_4791) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4792), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))))), inference(superposition, [status(thm), theory('equality')], [c_49534, c_50607])).
% 23.01/12.00  tff(c_50680, plain, (![B_4797, A_4798]: (v5_pre_topc(B_4797, A_4798, '#skF_2') | ~v5_pre_topc(B_4797, A_4798, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(B_4797, u1_struct_0(A_4798), '#skF_4') | ~m1_subset_1(B_4797, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4798), u1_struct_0('#skF_2')))) | ~v1_funct_2(B_4797, u1_struct_0(A_4798), u1_struct_0('#skF_2')) | ~v1_funct_1(B_4797) | ~l1_pre_topc(A_4798) | ~v2_pre_topc(A_4798) | ~v1_xboole_0(B_4797))), inference(demodulation, [status(thm), theory('equality')], [c_49692, c_47683, c_47689, c_49534, c_94, c_92, c_50618])).
% 23.01/12.00  tff(c_50690, plain, (![A_4798]: (v5_pre_topc('#skF_4', A_4798, '#skF_2') | ~v5_pre_topc('#skF_4', A_4798, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_4798), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_4798), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_4798) | ~v2_pre_topc(A_4798) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_50680])).
% 23.01/12.00  tff(c_51117, plain, (![A_4838]: (v5_pre_topc('#skF_4', A_4838, '#skF_2') | ~v5_pre_topc('#skF_4', A_4838, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_4838), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_4838), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_4838) | ~v2_pre_topc(A_4838))), inference(demodulation, [status(thm), theory('equality')], [c_49692, c_84, c_50690])).
% 23.01/12.00  tff(c_51121, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_50488, c_51117])).
% 23.01/12.00  tff(c_51127, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_49745, c_49534, c_49599, c_49534, c_49599, c_49534, c_51121])).
% 23.01/12.00  tff(c_51206, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_51127])).
% 23.01/12.00  tff(c_51209, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_51206])).
% 23.01/12.00  tff(c_51213, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_51209])).
% 23.01/12.00  tff(c_51215, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_51127])).
% 23.01/12.00  tff(c_49537, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_49534, c_47992])).
% 23.01/12.00  tff(c_49897, plain, (![D_4717, A_4718, B_4719]: (v5_pre_topc(D_4717, A_4718, B_4719) | ~v5_pre_topc(D_4717, g1_pre_topc(u1_struct_0(A_4718), u1_pre_topc(A_4718)), B_4719) | ~m1_subset_1(D_4717, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4718), u1_pre_topc(A_4718))), u1_struct_0(B_4719)))) | ~v1_funct_2(D_4717, u1_struct_0(g1_pre_topc(u1_struct_0(A_4718), u1_pre_topc(A_4718))), u1_struct_0(B_4719)) | ~m1_subset_1(D_4717, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4718), u1_struct_0(B_4719)))) | ~v1_funct_2(D_4717, u1_struct_0(A_4718), u1_struct_0(B_4719)) | ~v1_funct_1(D_4717) | ~l1_pre_topc(B_4719) | ~v2_pre_topc(B_4719) | ~l1_pre_topc(A_4718) | ~v2_pre_topc(A_4718))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_49919, plain, (![A_4718, B_4719]: (v5_pre_topc('#skF_4', A_4718, B_4719) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_4718), u1_pre_topc(A_4718)), B_4719) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_4718), u1_pre_topc(A_4718))), u1_struct_0(B_4719)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4718), u1_struct_0(B_4719)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_4718), u1_struct_0(B_4719)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_4719) | ~v2_pre_topc(B_4719) | ~l1_pre_topc(A_4718) | ~v2_pre_topc(A_4718))), inference(resolution, [status(thm)], [c_47687, c_49897])).
% 23.01/12.00  tff(c_51320, plain, (![A_4849, B_4850]: (v5_pre_topc('#skF_4', A_4849, B_4850) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_4849), u1_pre_topc(A_4849)), B_4850) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_4849), u1_pre_topc(A_4849))), u1_struct_0(B_4850)) | ~v1_funct_2('#skF_4', u1_struct_0(A_4849), u1_struct_0(B_4850)) | ~l1_pre_topc(B_4850) | ~v2_pre_topc(B_4850) | ~l1_pre_topc(A_4849) | ~v2_pre_topc(A_4849))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47687, c_49919])).
% 23.01/12.00  tff(c_51341, plain, (![B_4850]: (v5_pre_topc('#skF_4', '#skF_1', B_4850) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_4850) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_4850)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_4850)) | ~l1_pre_topc(B_4850) | ~v2_pre_topc(B_4850) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_47940, c_51320])).
% 23.01/12.00  tff(c_51360, plain, (![B_4851]: (v5_pre_topc('#skF_4', '#skF_1', B_4851) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), B_4851) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(B_4851)) | ~l1_pre_topc(B_4851) | ~v2_pre_topc(B_4851))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_49599, c_47940, c_47987, c_47940, c_47987, c_51341])).
% 23.01/12.00  tff(c_51366, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_49534, c_51360])).
% 23.01/12.00  tff(c_51372, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51215, c_49745, c_49537, c_48079, c_51366])).
% 23.01/12.00  tff(c_50701, plain, (![A_4798]: (v5_pre_topc('#skF_4', A_4798, '#skF_2') | ~v5_pre_topc('#skF_4', A_4798, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_4798), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_4798), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_4798) | ~v2_pre_topc(A_4798))), inference(demodulation, [status(thm), theory('equality')], [c_49692, c_84, c_50690])).
% 23.01/12.00  tff(c_51378, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51372, c_50701])).
% 23.01/12.00  tff(c_51381, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_49599, c_47940, c_49599, c_47940, c_51378])).
% 23.01/12.00  tff(c_51383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40401, c_51381])).
% 23.01/12.00  tff(c_51384, plain, (![B_4683]: (v1_xboole_0(B_4683))), inference(splitRight, [status(thm)], [c_49688])).
% 23.01/12.00  tff(c_51436, plain, (![A_4853]: (A_4853='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51384, c_47677])).
% 23.01/12.00  tff(c_49601, plain, (![A_4684, B_4685]: (v1_funct_2('#skF_4', A_4684, B_4685) | A_4684!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48204, c_49582])).
% 23.01/12.00  tff(c_48324, plain, (![B_4551, A_4553]: (B_4551='#skF_4' | v1_partfun1('#skF_4', A_4553) | ~v1_funct_2('#skF_4', A_4553, B_4551))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_48311])).
% 23.01/12.00  tff(c_49612, plain, (![B_4685, A_4684]: (B_4685='#skF_4' | v1_partfun1('#skF_4', A_4684) | A_4684!='#skF_4')), inference(resolution, [status(thm)], [c_49601, c_48324])).
% 23.01/12.00  tff(c_49620, plain, (![A_4686]: (v1_partfun1('#skF_4', A_4686) | A_4686!='#skF_4')), inference(splitLeft, [status(thm)], [c_49612])).
% 23.01/12.00  tff(c_49535, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_48336])).
% 23.01/12.00  tff(c_49627, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))!='#skF_4'), inference(resolution, [status(thm)], [c_49620, c_49535])).
% 23.01/12.00  tff(c_51557, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_51436, c_49627])).
% 23.01/12.00  tff(c_51559, plain, (![B_5424]: (B_5424='#skF_4')), inference(splitRight, [status(thm)], [c_49612])).
% 23.01/12.00  tff(c_51574, plain, (~v1_partfun1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_51559, c_49535])).
% 23.01/12.00  tff(c_51712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48199, c_51574])).
% 23.01/12.00  tff(c_51713, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_47935])).
% 23.01/12.00  tff(c_51717, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51713, c_107])).
% 23.01/12.00  tff(c_51911, plain, (![A_6208, B_6209, C_6210]: (k1_relset_1(A_6208, B_6209, C_6210)=k1_relat_1(C_6210) | ~m1_subset_1(C_6210, k1_zfmisc_1(k2_zfmisc_1(A_6208, B_6209))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_51926, plain, (![A_6208, B_6209]: (k1_relset_1(A_6208, B_6209, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_51911])).
% 23.01/12.00  tff(c_52053, plain, (![C_6238, A_6239, B_6240]: (v1_funct_2(C_6238, A_6239, B_6240) | k1_relset_1(A_6239, B_6240, C_6238)!=A_6239 | ~m1_subset_1(C_6238, k1_zfmisc_1(k2_zfmisc_1(A_6239, B_6240))) | ~v1_funct_1(C_6238))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_52057, plain, (![A_6239, B_6240]: (v1_funct_2('#skF_4', A_6239, B_6240) | k1_relset_1(A_6239, B_6240, '#skF_4')!=A_6239 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_52053])).
% 23.01/12.00  tff(c_52070, plain, (![A_6239, B_6240]: (v1_funct_2('#skF_4', A_6239, B_6240) | k1_relat_1('#skF_4')!=A_6239)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_51926, c_52057])).
% 23.01/12.00  tff(c_52632, plain, (![C_6862, A_6863, B_6864]: (~v1_xboole_0(C_6862) | ~v1_funct_2(C_6862, A_6863, B_6864) | ~v1_funct_1(C_6862) | ~m1_subset_1(C_6862, k1_zfmisc_1(k2_zfmisc_1(A_6863, B_6864))) | v1_xboole_0(B_6864) | v1_xboole_0(A_6863))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_52636, plain, (![A_6863, B_6864]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_6863, B_6864) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_6864) | v1_xboole_0(A_6863))), inference(resolution, [status(thm)], [c_47687, c_52632])).
% 23.01/12.00  tff(c_52666, plain, (![A_6866, B_6867]: (~v1_funct_2('#skF_4', A_6866, B_6867) | v1_xboole_0(B_6867) | v1_xboole_0(A_6866))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47664, c_52636])).
% 23.01/12.00  tff(c_52678, plain, (![B_6240, A_6239]: (v1_xboole_0(B_6240) | v1_xboole_0(A_6239) | k1_relat_1('#skF_4')!=A_6239)), inference(resolution, [status(thm)], [c_52070, c_52666])).
% 23.01/12.00  tff(c_52687, plain, (![A_6868]: (v1_xboole_0(A_6868) | k1_relat_1('#skF_4')!=A_6868)), inference(splitLeft, [status(thm)], [c_52678])).
% 23.01/12.00  tff(c_52723, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_52687, c_47677])).
% 23.01/12.00  tff(c_52075, plain, (![A_6241, B_6242]: (v1_funct_2('#skF_4', A_6241, B_6242) | k1_relat_1('#skF_4')!=A_6241)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_51926, c_52057])).
% 23.01/12.00  tff(c_51972, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, '#skF_4') | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_47683, c_47676, c_47676, c_47676, c_113])).
% 23.01/12.00  tff(c_52082, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_52075, c_51972])).
% 23.01/12.00  tff(c_52086, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47682, c_52082])).
% 23.01/12.00  tff(c_52087, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_52086])).
% 23.01/12.00  tff(c_52732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52723, c_52087])).
% 23.01/12.00  tff(c_52733, plain, (![B_6240]: (v1_xboole_0(B_6240))), inference(splitRight, [status(thm)], [c_52678])).
% 23.01/12.00  tff(c_52781, plain, (![A_6871]: (A_6871='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52733, c_47677])).
% 23.01/12.00  tff(c_52911, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_52781, c_52087])).
% 23.01/12.00  tff(c_52913, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_52086])).
% 23.01/12.00  tff(c_52945, plain, (![A_6239, B_6240]: (v1_funct_2('#skF_4', A_6239, B_6240) | A_6239!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52913, c_52070])).
% 23.01/12.00  tff(c_53013, plain, (![C_7441, A_7442, B_7443]: (~v1_xboole_0(C_7441) | ~v1_funct_2(C_7441, A_7442, B_7443) | ~v1_funct_1(C_7441) | ~m1_subset_1(C_7441, k1_zfmisc_1(k2_zfmisc_1(A_7442, B_7443))) | v1_xboole_0(B_7443) | v1_xboole_0(A_7442))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_53017, plain, (![A_7442, B_7443]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_7442, B_7443) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_7443) | v1_xboole_0(A_7442))), inference(resolution, [status(thm)], [c_47687, c_53013])).
% 23.01/12.00  tff(c_53047, plain, (![A_7445, B_7446]: (~v1_funct_2('#skF_4', A_7445, B_7446) | v1_xboole_0(B_7446) | v1_xboole_0(A_7445))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47664, c_53017])).
% 23.01/12.00  tff(c_53057, plain, (![B_6240, A_6239]: (v1_xboole_0(B_6240) | v1_xboole_0(A_6239) | A_6239!='#skF_4')), inference(resolution, [status(thm)], [c_52945, c_53047])).
% 23.01/12.00  tff(c_53061, plain, (![A_6239]: (v1_xboole_0(A_6239) | A_6239!='#skF_4')), inference(splitLeft, [status(thm)], [c_53057])).
% 23.01/12.00  tff(c_53063, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_53057])).
% 23.01/12.00  tff(c_52999, plain, (![B_6240]: (v1_funct_2('#skF_4', '#skF_4', B_6240))), inference(demodulation, [status(thm), theory('equality')], [c_52913, c_52070])).
% 23.01/12.00  tff(c_51729, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_51713, c_64])).
% 23.01/12.00  tff(c_51737, plain, (m1_subset_1(u1_pre_topc('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_47683, c_47683, c_51729])).
% 23.01/12.00  tff(c_51769, plain, (v1_xboole_0(u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_51737, c_47679])).
% 23.01/12.00  tff(c_51782, plain, (u1_pre_topc('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_51769, c_47677])).
% 23.01/12.00  tff(c_51716, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_51713, c_47740])).
% 23.01/12.00  tff(c_51854, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_51782, c_51716])).
% 23.01/12.00  tff(c_51718, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_51713, c_82])).
% 23.01/12.00  tff(c_51786, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_51782, c_51718])).
% 23.01/12.00  tff(c_53058, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_51786, c_53047])).
% 23.01/12.00  tff(c_53062, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_53058])).
% 23.01/12.00  tff(c_53129, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_53062, c_47677])).
% 23.01/12.00  tff(c_47697, plain, (![A_4468, B_4469]: (v1_pre_topc(g1_pre_topc(A_4468, B_4469)) | ~m1_subset_1(B_4469, k1_zfmisc_1(k1_zfmisc_1(A_4468))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/12.00  tff(c_47705, plain, (![A_45]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_45), u1_pre_topc(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_47697])).
% 23.01/12.00  tff(c_53190, plain, (v1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_53129, c_47705])).
% 23.01/12.00  tff(c_53576, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_53190])).
% 23.01/12.00  tff(c_53582, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40433, c_53576])).
% 23.01/12.00  tff(c_53587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_53582])).
% 23.01/12.00  tff(c_53589, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_53190])).
% 23.01/12.00  tff(c_53304, plain, (![D_7464, A_7465, B_7466]: (v5_pre_topc(D_7464, A_7465, g1_pre_topc(u1_struct_0(B_7466), u1_pre_topc(B_7466))) | ~v5_pre_topc(D_7464, A_7465, B_7466) | ~m1_subset_1(D_7464, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7465), u1_struct_0(g1_pre_topc(u1_struct_0(B_7466), u1_pre_topc(B_7466)))))) | ~v1_funct_2(D_7464, u1_struct_0(A_7465), u1_struct_0(g1_pre_topc(u1_struct_0(B_7466), u1_pre_topc(B_7466)))) | ~m1_subset_1(D_7464, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7465), u1_struct_0(B_7466)))) | ~v1_funct_2(D_7464, u1_struct_0(A_7465), u1_struct_0(B_7466)) | ~v1_funct_1(D_7464) | ~l1_pre_topc(B_7466) | ~v2_pre_topc(B_7466) | ~l1_pre_topc(A_7465) | ~v2_pre_topc(A_7465))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_54457, plain, (![B_7578, A_7579, B_7580]: (v5_pre_topc(B_7578, A_7579, g1_pre_topc(u1_struct_0(B_7580), u1_pre_topc(B_7580))) | ~v5_pre_topc(B_7578, A_7579, B_7580) | ~v1_funct_2(B_7578, u1_struct_0(A_7579), u1_struct_0(g1_pre_topc(u1_struct_0(B_7580), u1_pre_topc(B_7580)))) | ~m1_subset_1(B_7578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579), u1_struct_0(B_7580)))) | ~v1_funct_2(B_7578, u1_struct_0(A_7579), u1_struct_0(B_7580)) | ~v1_funct_1(B_7578) | ~l1_pre_topc(B_7580) | ~v2_pre_topc(B_7580) | ~l1_pre_topc(A_7579) | ~v2_pre_topc(A_7579) | ~v1_xboole_0(B_7578) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579), u1_struct_0(g1_pre_topc(u1_struct_0(B_7580), u1_pre_topc(B_7580)))))))), inference(resolution, [status(thm)], [c_16, c_53304])).
% 23.01/12.00  tff(c_54465, plain, (![B_7578, A_7579]: (v5_pre_topc(B_7578, A_7579, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v5_pre_topc(B_7578, A_7579, '#skF_1') | ~v1_funct_2(B_7578, u1_struct_0(A_7579), '#skF_4') | ~m1_subset_1(B_7578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579), u1_struct_0('#skF_1')))) | ~v1_funct_2(B_7578, u1_struct_0(A_7579), u1_struct_0('#skF_1')) | ~v1_funct_1(B_7578) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~l1_pre_topc(A_7579) | ~v2_pre_topc(A_7579) | ~v1_xboole_0(B_7578) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7579), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))))))), inference(superposition, [status(thm), theory('equality')], [c_53129, c_54457])).
% 23.01/12.00  tff(c_54535, plain, (![B_7586, A_7587]: (v5_pre_topc(B_7586, A_7587, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v5_pre_topc(B_7586, A_7587, '#skF_1') | ~v1_funct_2(B_7586, u1_struct_0(A_7587), '#skF_4') | ~m1_subset_1(B_7586, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7587), u1_struct_0('#skF_1')))) | ~v1_funct_2(B_7586, u1_struct_0(A_7587), u1_struct_0('#skF_1')) | ~v1_funct_1(B_7586) | ~l1_pre_topc(A_7587) | ~v2_pre_topc(A_7587) | ~v1_xboole_0(B_7586))), inference(demodulation, [status(thm), theory('equality')], [c_53063, c_47683, c_47689, c_53129, c_98, c_96, c_54465])).
% 23.01/12.00  tff(c_54545, plain, (![A_7587]: (v5_pre_topc('#skF_4', A_7587, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v5_pre_topc('#skF_4', A_7587, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0(A_7587), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_7587), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_7587) | ~v2_pre_topc(A_7587) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_54535])).
% 23.01/12.00  tff(c_54558, plain, (![A_7588]: (v5_pre_topc('#skF_4', A_7588, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v5_pre_topc('#skF_4', A_7588, '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0(A_7588), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_7588), u1_struct_0('#skF_1')) | ~l1_pre_topc(A_7588) | ~v2_pre_topc(A_7588))), inference(demodulation, [status(thm), theory('equality')], [c_53063, c_84, c_54545])).
% 23.01/12.00  tff(c_53397, plain, (![D_7478, A_7479, B_7480]: (v5_pre_topc(D_7478, A_7479, B_7480) | ~v5_pre_topc(D_7478, g1_pre_topc(u1_struct_0(A_7479), u1_pre_topc(A_7479)), B_7480) | ~m1_subset_1(D_7478, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_7479), u1_pre_topc(A_7479))), u1_struct_0(B_7480)))) | ~v1_funct_2(D_7478, u1_struct_0(g1_pre_topc(u1_struct_0(A_7479), u1_pre_topc(A_7479))), u1_struct_0(B_7480)) | ~m1_subset_1(D_7478, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7479), u1_struct_0(B_7480)))) | ~v1_funct_2(D_7478, u1_struct_0(A_7479), u1_struct_0(B_7480)) | ~v1_funct_1(D_7478) | ~l1_pre_topc(B_7480) | ~v2_pre_topc(B_7480) | ~l1_pre_topc(A_7479) | ~v2_pre_topc(A_7479))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_54150, plain, (![B_7553, A_7554, B_7555]: (v5_pre_topc(B_7553, A_7554, B_7555) | ~v5_pre_topc(B_7553, g1_pre_topc(u1_struct_0(A_7554), u1_pre_topc(A_7554)), B_7555) | ~v1_funct_2(B_7553, u1_struct_0(g1_pre_topc(u1_struct_0(A_7554), u1_pre_topc(A_7554))), u1_struct_0(B_7555)) | ~m1_subset_1(B_7553, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7554), u1_struct_0(B_7555)))) | ~v1_funct_2(B_7553, u1_struct_0(A_7554), u1_struct_0(B_7555)) | ~v1_funct_1(B_7553) | ~l1_pre_topc(B_7555) | ~v2_pre_topc(B_7555) | ~l1_pre_topc(A_7554) | ~v2_pre_topc(A_7554) | ~v1_xboole_0(B_7553) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_7554), u1_pre_topc(A_7554))), u1_struct_0(B_7555)))))), inference(resolution, [status(thm)], [c_16, c_53397])).
% 23.01/12.00  tff(c_54156, plain, (![B_7553, B_7555]: (v5_pre_topc(B_7553, '#skF_1', B_7555) | ~v5_pre_topc(B_7553, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7555) | ~v1_funct_2(B_7553, '#skF_4', u1_struct_0(B_7555)) | ~m1_subset_1(B_7553, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_7555)))) | ~v1_funct_2(B_7553, u1_struct_0('#skF_1'), u1_struct_0(B_7555)) | ~v1_funct_1(B_7553) | ~l1_pre_topc(B_7555) | ~v2_pre_topc(B_7555) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~v1_xboole_0(B_7553) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_7555)))))), inference(superposition, [status(thm), theory('equality')], [c_53129, c_54150])).
% 23.01/12.00  tff(c_54295, plain, (![B_7565, B_7566]: (v5_pre_topc(B_7565, '#skF_1', B_7566) | ~v5_pre_topc(B_7565, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7566) | ~v1_funct_2(B_7565, '#skF_4', u1_struct_0(B_7566)) | ~m1_subset_1(B_7565, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_7566)))) | ~v1_funct_2(B_7565, u1_struct_0('#skF_1'), u1_struct_0(B_7566)) | ~v1_funct_1(B_7565) | ~l1_pre_topc(B_7566) | ~v2_pre_topc(B_7566) | ~v1_xboole_0(B_7565))), inference(demodulation, [status(thm), theory('equality')], [c_53063, c_47683, c_47688, c_53129, c_98, c_96, c_54156])).
% 23.01/12.00  tff(c_54305, plain, (![B_7566]: (v5_pre_topc('#skF_4', '#skF_1', B_7566) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7566) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_7566)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_7566)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_7566) | ~v2_pre_topc(B_7566) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_54295])).
% 23.01/12.00  tff(c_54316, plain, (![B_7566]: (v5_pre_topc('#skF_4', '#skF_1', B_7566) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7566) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_7566)) | ~l1_pre_topc(B_7566) | ~v2_pre_topc(B_7566))), inference(demodulation, [status(thm), theory('equality')], [c_53063, c_84, c_52999, c_54305])).
% 23.01/12.00  tff(c_54562, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0('#skF_1')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(resolution, [status(thm)], [c_54558, c_54316])).
% 23.01/12.00  tff(c_54565, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_1') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_53589, c_52999, c_53129, c_52999, c_53129, c_51717, c_53129, c_54562])).
% 23.01/12.00  tff(c_54566, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_54565])).
% 23.01/12.00  tff(c_54569, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_54566])).
% 23.01/12.00  tff(c_54573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_54569])).
% 23.01/12.00  tff(c_54575, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_54565])).
% 23.01/12.00  tff(c_53132, plain, (![D_7453, A_7454, B_7455]: (v5_pre_topc(D_7453, A_7454, B_7455) | ~v5_pre_topc(D_7453, A_7454, g1_pre_topc(u1_struct_0(B_7455), u1_pre_topc(B_7455))) | ~m1_subset_1(D_7453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7454), u1_struct_0(g1_pre_topc(u1_struct_0(B_7455), u1_pre_topc(B_7455)))))) | ~v1_funct_2(D_7453, u1_struct_0(A_7454), u1_struct_0(g1_pre_topc(u1_struct_0(B_7455), u1_pre_topc(B_7455)))) | ~m1_subset_1(D_7453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7454), u1_struct_0(B_7455)))) | ~v1_funct_2(D_7453, u1_struct_0(A_7454), u1_struct_0(B_7455)) | ~v1_funct_1(D_7453) | ~l1_pre_topc(B_7455) | ~v2_pre_topc(B_7455) | ~l1_pre_topc(A_7454) | ~v2_pre_topc(A_7454))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_53145, plain, (![A_7454, B_7455]: (v5_pre_topc('#skF_4', A_7454, B_7455) | ~v5_pre_topc('#skF_4', A_7454, g1_pre_topc(u1_struct_0(B_7455), u1_pre_topc(B_7455))) | ~v1_funct_2('#skF_4', u1_struct_0(A_7454), u1_struct_0(g1_pre_topc(u1_struct_0(B_7455), u1_pre_topc(B_7455)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7454), u1_struct_0(B_7455)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_7454), u1_struct_0(B_7455)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_7455) | ~v2_pre_topc(B_7455) | ~l1_pre_topc(A_7454) | ~v2_pre_topc(A_7454))), inference(resolution, [status(thm)], [c_47687, c_53132])).
% 23.01/12.00  tff(c_54728, plain, (![A_7599, B_7600]: (v5_pre_topc('#skF_4', A_7599, B_7600) | ~v5_pre_topc('#skF_4', A_7599, g1_pre_topc(u1_struct_0(B_7600), u1_pre_topc(B_7600))) | ~v1_funct_2('#skF_4', u1_struct_0(A_7599), u1_struct_0(g1_pre_topc(u1_struct_0(B_7600), u1_pre_topc(B_7600)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_7599), u1_struct_0(B_7600)) | ~l1_pre_topc(B_7600) | ~v2_pre_topc(B_7600) | ~l1_pre_topc(A_7599) | ~v2_pre_topc(A_7599))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_47687, c_53145])).
% 23.01/12.00  tff(c_54734, plain, (![B_7600]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7600) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_7600), u1_pre_topc(B_7600))) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_7600), u1_pre_topc(B_7600)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_7600)) | ~l1_pre_topc(B_7600) | ~v2_pre_topc(B_7600) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_53129, c_54728])).
% 23.01/12.00  tff(c_54804, plain, (![B_7602]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_7602) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_7602), u1_pre_topc(B_7602))) | ~l1_pre_topc(B_7602) | ~v2_pre_topc(B_7602))), inference(demodulation, [status(thm), theory('equality')], [c_54575, c_53589, c_52999, c_53129, c_52999, c_54734])).
% 23.01/12.00  tff(c_54820, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_51782, c_54804])).
% 23.01/12.00  tff(c_54834, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_51854, c_51713, c_54820])).
% 23.01/12.00  tff(c_54301, plain, (![B_7565]: (v5_pre_topc(B_7565, '#skF_1', '#skF_2') | ~v5_pre_topc(B_7565, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2(B_7565, '#skF_4', u1_struct_0('#skF_2')) | ~m1_subset_1(B_7565, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))) | ~v1_funct_2(B_7565, u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(B_7565) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~v1_xboole_0(B_7565))), inference(superposition, [status(thm), theory('equality')], [c_51713, c_54295])).
% 23.01/12.00  tff(c_54313, plain, (![B_7565]: (v5_pre_topc(B_7565, '#skF_1', '#skF_2') | ~v5_pre_topc(B_7565, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~v1_funct_2(B_7565, '#skF_4', '#skF_4') | ~m1_subset_1(B_7565, '#skF_4') | ~v1_funct_2(B_7565, u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1(B_7565) | ~v1_xboole_0(B_7565))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_51713, c_47683, c_47689, c_51713, c_54301])).
% 23.01/12.00  tff(c_54839, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_54834, c_54313])).
% 23.01/12.00  tff(c_54845, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_53063, c_84, c_51717, c_47682, c_52999, c_54839])).
% 23.01/12.00  tff(c_54847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40401, c_54845])).
% 23.01/12.00  tff(c_54849, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_53058])).
% 23.01/12.00  tff(c_55098, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))!='#skF_4'), inference(resolution, [status(thm)], [c_53061, c_54849])).
% 23.01/12.00  tff(c_51996, plain, (![B_6227, C_6228, A_6229]: (B_6227='#skF_4' | v1_partfun1(C_6228, A_6229) | ~v1_funct_2(C_6228, A_6229, B_6227) | ~m1_subset_1(C_6228, k1_zfmisc_1(k2_zfmisc_1(A_6229, B_6227))) | ~v1_funct_1(C_6228))), inference(demodulation, [status(thm), theory('equality')], [c_47676, c_58])).
% 23.01/12.00  tff(c_52000, plain, (![B_6227, A_6229]: (B_6227='#skF_4' | v1_partfun1('#skF_4', A_6229) | ~v1_funct_2('#skF_4', A_6229, B_6227) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_47687, c_51996])).
% 23.01/12.00  tff(c_52018, plain, (![B_6230, A_6231]: (B_6230='#skF_4' | v1_partfun1('#skF_4', A_6231) | ~v1_funct_2('#skF_4', A_6231, B_6230))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_52000])).
% 23.01/12.00  tff(c_52025, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_51786, c_52018])).
% 23.01/12.00  tff(c_52970, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitLeft, [status(thm)], [c_52025])).
% 23.01/12.00  tff(c_51877, plain, (![B_6202, A_6203]: (k1_relat_1(B_6202)=A_6203 | ~v1_partfun1(B_6202, A_6203) | ~v4_relat_1(B_6202, A_6203) | ~v1_relat_1(B_6202))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_51883, plain, (![A_4483]: (k1_relat_1('#skF_4')=A_4483 | ~v1_partfun1('#skF_4', A_4483) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_47873, c_51877])).
% 23.01/12.00  tff(c_51887, plain, (![A_4483]: (k1_relat_1('#skF_4')=A_4483 | ~v1_partfun1('#skF_4', A_4483))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_51883])).
% 23.01/12.00  tff(c_52947, plain, (![A_4483]: (A_4483='#skF_4' | ~v1_partfun1('#skF_4', A_4483))), inference(demodulation, [status(thm), theory('equality')], [c_52913, c_51887])).
% 23.01/12.00  tff(c_55172, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_52970, c_52947])).
% 23.01/12.00  tff(c_55179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55098, c_55172])).
% 23.01/12.00  tff(c_55180, plain, (![B_6240]: (v1_xboole_0(B_6240))), inference(splitRight, [status(thm)], [c_53057])).
% 23.01/12.00  tff(c_55228, plain, (![A_7621]: (A_7621='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55180, c_47677])).
% 23.01/12.00  tff(c_51714, plain, (u1_struct_0('#skF_1')!='#skF_4'), inference(splitRight, [status(thm)], [c_47935])).
% 23.01/12.00  tff(c_55358, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_55228, c_51714])).
% 23.01/12.00  tff(c_55359, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_52025])).
% 23.01/12.00  tff(c_55410, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55359, c_51786])).
% 23.01/12.00  tff(c_51841, plain, (![A_6191]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_6191), u1_pre_topc(A_6191))) | ~l1_pre_topc(A_6191) | ~v2_pre_topc(A_6191))), inference(cnfTransformation, [status(thm)], [f_178])).
% 23.01/12.00  tff(c_51847, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_51713, c_51841])).
% 23.01/12.00  tff(c_51851, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_51782, c_51847])).
% 23.01/12.00  tff(c_55509, plain, (![D_8158, A_8159, B_8160]: (v5_pre_topc(D_8158, A_8159, B_8160) | ~v5_pre_topc(D_8158, g1_pre_topc(u1_struct_0(A_8159), u1_pre_topc(A_8159)), B_8160) | ~m1_subset_1(D_8158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_8159), u1_pre_topc(A_8159))), u1_struct_0(B_8160)))) | ~v1_funct_2(D_8158, u1_struct_0(g1_pre_topc(u1_struct_0(A_8159), u1_pre_topc(A_8159))), u1_struct_0(B_8160)) | ~m1_subset_1(D_8158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8159), u1_struct_0(B_8160)))) | ~v1_funct_2(D_8158, u1_struct_0(A_8159), u1_struct_0(B_8160)) | ~v1_funct_1(D_8158) | ~l1_pre_topc(B_8160) | ~v2_pre_topc(B_8160) | ~l1_pre_topc(A_8159) | ~v2_pre_topc(A_8159))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_55518, plain, (![D_8158, A_8159]: (v5_pre_topc(D_8158, A_8159, g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_8158, g1_pre_topc(u1_struct_0(A_8159), u1_pre_topc(A_8159)), g1_pre_topc('#skF_4', '#skF_4')) | ~m1_subset_1(D_8158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_8159), u1_pre_topc(A_8159))), '#skF_4'))) | ~v1_funct_2(D_8158, u1_struct_0(g1_pre_topc(u1_struct_0(A_8159), u1_pre_topc(A_8159))), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | ~m1_subset_1(D_8158, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8159), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))))) | ~v1_funct_2(D_8158, u1_struct_0(A_8159), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | ~v1_funct_1(D_8158) | ~l1_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~l1_pre_topc(A_8159) | ~v2_pre_topc(A_8159))), inference(superposition, [status(thm), theory('equality')], [c_55359, c_55509])).
% 23.01/12.00  tff(c_55869, plain, (![D_8187, A_8188]: (v5_pre_topc(D_8187, A_8188, g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_8187, g1_pre_topc(u1_struct_0(A_8188), u1_pre_topc(A_8188)), g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2(D_8187, u1_struct_0(g1_pre_topc(u1_struct_0(A_8188), u1_pre_topc(A_8188))), '#skF_4') | ~m1_subset_1(D_8187, '#skF_4') | ~v1_funct_2(D_8187, u1_struct_0(A_8188), '#skF_4') | ~v1_funct_1(D_8187) | ~l1_pre_topc(A_8188) | ~v2_pre_topc(A_8188))), inference(demodulation, [status(thm), theory('equality')], [c_51851, c_47681, c_55359, c_47683, c_47689, c_55359, c_55359, c_47683, c_47689, c_55518])).
% 23.01/12.00  tff(c_55878, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_51854, c_55869])).
% 23.01/12.00  tff(c_55891, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_51717, c_47682, c_55410, c_55878])).
% 23.01/12.00  tff(c_55589, plain, (![D_8164, A_8165, B_8166]: (v5_pre_topc(D_8164, A_8165, B_8166) | ~v5_pre_topc(D_8164, A_8165, g1_pre_topc(u1_struct_0(B_8166), u1_pre_topc(B_8166))) | ~m1_subset_1(D_8164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165), u1_struct_0(g1_pre_topc(u1_struct_0(B_8166), u1_pre_topc(B_8166)))))) | ~v1_funct_2(D_8164, u1_struct_0(A_8165), u1_struct_0(g1_pre_topc(u1_struct_0(B_8166), u1_pre_topc(B_8166)))) | ~m1_subset_1(D_8164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165), u1_struct_0(B_8166)))) | ~v1_funct_2(D_8164, u1_struct_0(A_8165), u1_struct_0(B_8166)) | ~v1_funct_1(D_8164) | ~l1_pre_topc(B_8166) | ~v2_pre_topc(B_8166) | ~l1_pre_topc(A_8165) | ~v2_pre_topc(A_8165))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_55601, plain, (![D_8164, A_8165]: (v5_pre_topc(D_8164, A_8165, '#skF_2') | ~v5_pre_topc(D_8164, A_8165, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1(D_8164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), '#skF_4'))))) | ~v1_funct_2(D_8164, u1_struct_0(A_8165), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_8164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8165), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_8164, u1_struct_0(A_8165), u1_struct_0('#skF_2')) | ~v1_funct_1(D_8164) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_8165) | ~v2_pre_topc(A_8165))), inference(superposition, [status(thm), theory('equality')], [c_51782, c_55589])).
% 23.01/12.00  tff(c_56898, plain, (![D_8301, A_8302]: (v5_pre_topc(D_8301, A_8302, '#skF_2') | ~v5_pre_topc(D_8301, A_8302, g1_pre_topc('#skF_4', '#skF_4')) | ~m1_subset_1(D_8301, '#skF_4') | ~v1_funct_2(D_8301, u1_struct_0(A_8302), '#skF_4') | ~v1_funct_1(D_8301) | ~l1_pre_topc(A_8302) | ~v2_pre_topc(A_8302))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_51713, c_47683, c_47689, c_51713, c_55359, c_51713, c_51782, c_47683, c_47689, c_55359, c_51713, c_51713, c_51782, c_55601])).
% 23.01/12.00  tff(c_56910, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_55891, c_56898])).
% 23.01/12.00  tff(c_56923, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_51717, c_47682, c_56910])).
% 23.01/12.00  tff(c_56925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40401, c_56923])).
% 23.01/12.00  tff(c_56927, plain, (v5_pre_topc('#skF_4', '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_110])).
% 23.01/12.00  tff(c_57030, plain, (![C_8321, A_8322, B_8323]: (v4_relat_1(C_8321, A_8322) | ~m1_subset_1(C_8321, k1_zfmisc_1(k2_zfmisc_1(A_8322, B_8323))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/12.00  tff(c_57052, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_111, c_57030])).
% 23.01/12.00  tff(c_57137, plain, (![B_8340, A_8341]: (k1_relat_1(B_8340)=A_8341 | ~v1_partfun1(B_8340, A_8341) | ~v4_relat_1(B_8340, A_8341) | ~v1_relat_1(B_8340))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_57146, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_57052, c_57137])).
% 23.01/12.00  tff(c_57156, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_57146])).
% 23.01/12.00  tff(c_57166, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_57156])).
% 23.01/12.00  tff(c_57465, plain, (![B_8415, C_8416, A_8417]: (k1_xboole_0=B_8415 | v1_partfun1(C_8416, A_8417) | ~v1_funct_2(C_8416, A_8417, B_8415) | ~m1_subset_1(C_8416, k1_zfmisc_1(k2_zfmisc_1(A_8417, B_8415))) | ~v1_funct_1(C_8416))), inference(cnfTransformation, [status(thm)], [f_160])).
% 23.01/12.00  tff(c_57471, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_111, c_57465])).
% 23.01/12.00  tff(c_57491, plain, (u1_struct_0('#skF_2')=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_57471])).
% 23.01/12.00  tff(c_57492, plain, (u1_struct_0('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_57166, c_57491])).
% 23.01/12.00  tff(c_57063, plain, (![C_8329, B_8330, A_8331]: (v1_xboole_0(C_8329) | ~m1_subset_1(C_8329, k1_zfmisc_1(k2_zfmisc_1(B_8330, A_8331))) | ~v1_xboole_0(A_8331))), inference(cnfTransformation, [status(thm)], [f_85])).
% 23.01/12.00  tff(c_57085, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_111, c_57063])).
% 23.01/12.00  tff(c_57111, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_57085])).
% 23.01/12.00  tff(c_57506, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_57492, c_57111])).
% 23.01/12.00  tff(c_57518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_57506])).
% 23.01/12.00  tff(c_57519, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_57156])).
% 23.01/12.00  tff(c_56926, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_110])).
% 23.01/12.00  tff(c_57572, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_57519, c_56926])).
% 23.01/12.00  tff(c_57084, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_80, c_57063])).
% 23.01/12.00  tff(c_57118, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_57084])).
% 23.01/12.00  tff(c_57528, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_57519, c_82])).
% 23.01/12.00  tff(c_57525, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_57519, c_80])).
% 23.01/12.00  tff(c_57785, plain, (![C_8443, A_8444, B_8445]: (v1_partfun1(C_8443, A_8444) | ~v1_funct_2(C_8443, A_8444, B_8445) | ~v1_funct_1(C_8443) | ~m1_subset_1(C_8443, k1_zfmisc_1(k2_zfmisc_1(A_8444, B_8445))) | v1_xboole_0(B_8445))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_57791, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_57525, c_57785])).
% 23.01/12.00  tff(c_57812, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_57528, c_57791])).
% 23.01/12.00  tff(c_57813, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))))), inference(negUnitSimplification, [status(thm)], [c_57118, c_57812])).
% 23.01/12.00  tff(c_57051, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(resolution, [status(thm)], [c_80, c_57030])).
% 23.01/12.00  tff(c_57140, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_57051, c_57137])).
% 23.01/12.00  tff(c_57152, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_57140])).
% 23.01/12.00  tff(c_58185, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57813, c_57519, c_57519, c_57152])).
% 23.01/12.00  tff(c_58193, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_58185, c_57528])).
% 23.01/12.00  tff(c_58192, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))))), inference(demodulation, [status(thm), theory('equality')], [c_58185, c_57525])).
% 23.01/12.00  tff(c_59376, plain, (![D_8582, A_8583, B_8584]: (v5_pre_topc(D_8582, g1_pre_topc(u1_struct_0(A_8583), u1_pre_topc(A_8583)), B_8584) | ~v5_pre_topc(D_8582, A_8583, B_8584) | ~m1_subset_1(D_8582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_8583), u1_pre_topc(A_8583))), u1_struct_0(B_8584)))) | ~v1_funct_2(D_8582, u1_struct_0(g1_pre_topc(u1_struct_0(A_8583), u1_pre_topc(A_8583))), u1_struct_0(B_8584)) | ~m1_subset_1(D_8582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8583), u1_struct_0(B_8584)))) | ~v1_funct_2(D_8582, u1_struct_0(A_8583), u1_struct_0(B_8584)) | ~v1_funct_1(D_8582) | ~l1_pre_topc(B_8584) | ~v2_pre_topc(B_8584) | ~l1_pre_topc(A_8583) | ~v2_pre_topc(A_8583))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_59385, plain, (![D_8582, B_8584]: (v5_pre_topc(D_8582, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_8584) | ~v5_pre_topc(D_8582, '#skF_1', B_8584) | ~m1_subset_1(D_8582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1'))), u1_struct_0(B_8584)))) | ~v1_funct_2(D_8582, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_8584)) | ~m1_subset_1(D_8582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_8584)))) | ~v1_funct_2(D_8582, u1_struct_0('#skF_1'), u1_struct_0(B_8584)) | ~v1_funct_1(D_8582) | ~l1_pre_topc(B_8584) | ~v2_pre_topc(B_8584) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_57519, c_59376])).
% 23.01/12.00  tff(c_60088, plain, (![D_8650, B_8651]: (v5_pre_topc(D_8650, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), B_8651) | ~v5_pre_topc(D_8650, '#skF_1', B_8651) | ~m1_subset_1(D_8650, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_8651)))) | ~v1_funct_2(D_8650, k1_relat_1('#skF_4'), u1_struct_0(B_8651)) | ~v1_funct_1(D_8650) | ~l1_pre_topc(B_8651) | ~v2_pre_topc(B_8651))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_57519, c_57519, c_58185, c_57519, c_58185, c_57519, c_59385])).
% 23.01/12.00  tff(c_60091, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_58192, c_60088])).
% 23.01/12.00  tff(c_60111, plain, (v5_pre_topc('#skF_4', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_58193, c_60091])).
% 23.01/12.00  tff(c_60112, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_57572, c_60111])).
% 23.01/12.00  tff(c_60122, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_60112])).
% 23.01/12.00  tff(c_60125, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_60122])).
% 23.01/12.00  tff(c_60129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_60125])).
% 23.01/12.00  tff(c_60130, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_60112])).
% 23.01/12.00  tff(c_60132, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_60130])).
% 23.01/12.00  tff(c_57527, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_57519, c_107])).
% 23.01/12.00  tff(c_57526, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_57519, c_111])).
% 23.01/12.00  tff(c_58249, plain, (![D_8508, A_8509, B_8510]: (v5_pre_topc(D_8508, A_8509, g1_pre_topc(u1_struct_0(B_8510), u1_pre_topc(B_8510))) | ~v5_pre_topc(D_8508, A_8509, B_8510) | ~m1_subset_1(D_8508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8509), u1_struct_0(g1_pre_topc(u1_struct_0(B_8510), u1_pre_topc(B_8510)))))) | ~v1_funct_2(D_8508, u1_struct_0(A_8509), u1_struct_0(g1_pre_topc(u1_struct_0(B_8510), u1_pre_topc(B_8510)))) | ~m1_subset_1(D_8508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8509), u1_struct_0(B_8510)))) | ~v1_funct_2(D_8508, u1_struct_0(A_8509), u1_struct_0(B_8510)) | ~v1_funct_1(D_8508) | ~l1_pre_topc(B_8510) | ~v2_pre_topc(B_8510) | ~l1_pre_topc(A_8509) | ~v2_pre_topc(A_8509))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_58258, plain, (![D_8508, B_8510]: (v5_pre_topc(D_8508, '#skF_1', g1_pre_topc(u1_struct_0(B_8510), u1_pre_topc(B_8510))) | ~v5_pre_topc(D_8508, '#skF_1', B_8510) | ~m1_subset_1(D_8508, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_8510), u1_pre_topc(B_8510)))))) | ~v1_funct_2(D_8508, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_8510), u1_pre_topc(B_8510)))) | ~m1_subset_1(D_8508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_8510)))) | ~v1_funct_2(D_8508, u1_struct_0('#skF_1'), u1_struct_0(B_8510)) | ~v1_funct_1(D_8508) | ~l1_pre_topc(B_8510) | ~v2_pre_topc(B_8510) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_57519, c_58249])).
% 23.01/12.00  tff(c_60431, plain, (![D_8683, B_8684]: (v5_pre_topc(D_8683, '#skF_1', g1_pre_topc(u1_struct_0(B_8684), u1_pre_topc(B_8684))) | ~v5_pre_topc(D_8683, '#skF_1', B_8684) | ~m1_subset_1(D_8683, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_8684), u1_pre_topc(B_8684)))))) | ~v1_funct_2(D_8683, k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_8684), u1_pre_topc(B_8684)))) | ~m1_subset_1(D_8683, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_8684)))) | ~v1_funct_2(D_8683, k1_relat_1('#skF_4'), u1_struct_0(B_8684)) | ~v1_funct_1(D_8683) | ~l1_pre_topc(B_8684) | ~v2_pre_topc(B_8684))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_57519, c_57519, c_57519, c_58258])).
% 23.01/12.00  tff(c_60437, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58192, c_60431])).
% 23.01/12.00  tff(c_60456, plain, (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_57527, c_57526, c_58193, c_56927, c_60437])).
% 23.01/12.00  tff(c_60458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60132, c_60456])).
% 23.01/12.00  tff(c_60459, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_60130])).
% 23.01/12.00  tff(c_60463, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56959, c_60459])).
% 23.01/12.00  tff(c_60467, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_60463])).
% 23.01/12.00  tff(c_60468, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_57084])).
% 23.01/12.00  tff(c_60480, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60468, c_144])).
% 23.01/12.00  tff(c_60500, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60480, c_60480, c_8])).
% 23.01/12.00  tff(c_60469, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitRight, [status(thm)], [c_57084])).
% 23.01/12.00  tff(c_60481, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_60468, c_4])).
% 23.01/12.00  tff(c_60690, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(resolution, [status(thm)], [c_60469, c_60481])).
% 23.01/12.00  tff(c_57060, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))), inference(splitLeft, [status(thm)], [c_198])).
% 23.01/12.00  tff(c_60814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60468, c_60500, c_60690, c_57060])).
% 23.01/12.00  tff(c_60815, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_57085])).
% 23.01/12.00  tff(c_60827, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60815, c_144])).
% 23.01/12.00  tff(c_60846, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60827, c_60827, c_8])).
% 23.01/12.00  tff(c_60816, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_57085])).
% 23.01/12.00  tff(c_60901, plain, (![A_8720]: (A_8720='#skF_4' | ~v1_xboole_0(A_8720))), inference(resolution, [status(thm)], [c_60815, c_4])).
% 23.01/12.00  tff(c_60908, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_60816, c_60901])).
% 23.01/12.00  tff(c_56976, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_60914, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60908, c_56976])).
% 23.01/12.00  tff(c_61138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60815, c_60846, c_60914])).
% 23.01/12.00  tff(c_61139, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_198])).
% 23.01/12.00  tff(c_61151, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_61139, c_144])).
% 23.01/12.00  tff(c_61169, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61151, c_61151, c_10])).
% 23.01/12.00  tff(c_61168, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_61151, c_20])).
% 23.01/12.00  tff(c_61469, plain, (![A_8779, B_8780, C_8781]: (k1_relset_1(A_8779, B_8780, C_8781)=k1_relat_1(C_8781) | ~m1_subset_1(C_8781, k1_zfmisc_1(k2_zfmisc_1(A_8779, B_8780))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_61484, plain, (![A_8779, B_8780]: (k1_relset_1(A_8779, B_8780, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_61168, c_61469])).
% 23.01/12.00  tff(c_61776, plain, (![C_8820, A_8821, B_8822]: (v1_funct_2(C_8820, A_8821, B_8822) | k1_relset_1(A_8821, B_8822, C_8820)!=A_8821 | ~m1_subset_1(C_8820, k1_zfmisc_1(k2_zfmisc_1(A_8821, B_8822))) | ~v1_funct_1(C_8820))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_61780, plain, (![A_8821, B_8822]: (v1_funct_2('#skF_4', A_8821, B_8822) | k1_relset_1(A_8821, B_8822, '#skF_4')!=A_8821 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_61168, c_61776])).
% 23.01/12.00  tff(c_61793, plain, (![A_8821, B_8822]: (v1_funct_2('#skF_4', A_8821, B_8822) | k1_relat_1('#skF_4')!=A_8821)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_61484, c_61780])).
% 23.01/12.00  tff(c_62103, plain, (![C_8835, A_8836, B_8837]: (~v1_xboole_0(C_8835) | ~v1_funct_2(C_8835, A_8836, B_8837) | ~v1_funct_1(C_8835) | ~m1_subset_1(C_8835, k1_zfmisc_1(k2_zfmisc_1(A_8836, B_8837))) | v1_xboole_0(B_8837) | v1_xboole_0(A_8836))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_62107, plain, (![A_8836, B_8837]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_8836, B_8837) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_8837) | v1_xboole_0(A_8836))), inference(resolution, [status(thm)], [c_61168, c_62103])).
% 23.01/12.00  tff(c_62323, plain, (![A_8843, B_8844]: (~v1_funct_2('#skF_4', A_8843, B_8844) | v1_xboole_0(B_8844) | v1_xboole_0(A_8843))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_61139, c_62107])).
% 23.01/12.00  tff(c_62327, plain, (![B_8822, A_8821]: (v1_xboole_0(B_8822) | v1_xboole_0(A_8821) | k1_relat_1('#skF_4')!=A_8821)), inference(resolution, [status(thm)], [c_61793, c_62323])).
% 23.01/12.00  tff(c_62371, plain, (![A_8848]: (v1_xboole_0(A_8848) | k1_relat_1('#skF_4')!=A_8848)), inference(splitLeft, [status(thm)], [c_62327])).
% 23.01/12.00  tff(c_61152, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_61139, c_4])).
% 23.01/12.00  tff(c_62429, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_62371, c_61152])).
% 23.01/12.00  tff(c_61163, plain, (m1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61151, c_61151, c_40388])).
% 23.01/12.00  tff(c_61811, plain, (![A_8823, B_8824]: (v1_funct_2('#skF_4', A_8823, B_8824) | k1_relat_1('#skF_4')!=A_8823)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_61484, c_61780])).
% 23.01/12.00  tff(c_61164, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61151, c_61151, c_40375])).
% 23.01/12.00  tff(c_61568, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, '#skF_4') | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_61164, c_61151, c_61151, c_61151, c_113])).
% 23.01/12.00  tff(c_61818, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_61811, c_61568])).
% 23.01/12.00  tff(c_61822, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_61163, c_61818])).
% 23.01/12.00  tff(c_61846, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_61822])).
% 23.01/12.00  tff(c_62447, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62429, c_61846])).
% 23.01/12.00  tff(c_62448, plain, (![B_8822]: (v1_xboole_0(B_8822))), inference(splitRight, [status(thm)], [c_62327])).
% 23.01/12.00  tff(c_61170, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61151, c_61151, c_8])).
% 23.01/12.00  tff(c_61647, plain, (![C_8815, A_8816, B_8817]: (v1_partfun1(C_8815, A_8816) | ~v1_funct_2(C_8815, A_8816, B_8817) | ~v1_funct_1(C_8815) | ~m1_subset_1(C_8815, k1_zfmisc_1(k2_zfmisc_1(A_8816, B_8817))) | v1_xboole_0(B_8817))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_61651, plain, (![A_8816, B_8817]: (v1_partfun1('#skF_4', A_8816) | ~v1_funct_2('#skF_4', A_8816, B_8817) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_8817))), inference(resolution, [status(thm)], [c_61168, c_61647])).
% 23.01/12.00  tff(c_61668, plain, (![A_8818, B_8819]: (v1_partfun1('#skF_4', A_8818) | ~v1_funct_2('#skF_4', A_8818, B_8819) | v1_xboole_0(B_8819))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_61651])).
% 23.01/12.00  tff(c_61675, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_107, c_61668])).
% 23.01/12.00  tff(c_61677, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_61675])).
% 23.01/12.00  tff(c_61692, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_61677, c_61152])).
% 23.01/12.00  tff(c_61700, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_61692, c_56976])).
% 23.01/12.00  tff(c_61707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61139, c_61170, c_61700])).
% 23.01/12.00  tff(c_61708, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_61675])).
% 23.01/12.00  tff(c_61223, plain, (![A_8735]: (k2_zfmisc_1(A_8735, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61151, c_61151, c_8])).
% 23.01/12.00  tff(c_30, plain, (![C_19, A_17, B_18]: (v4_relat_1(C_19, A_17) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/12.00  tff(c_61228, plain, (![C_19, A_8735]: (v4_relat_1(C_19, A_8735) | ~m1_subset_1(C_19, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61223, c_30])).
% 23.01/12.00  tff(c_61237, plain, (![C_19, A_8735]: (v4_relat_1(C_19, A_8735) | ~m1_subset_1(C_19, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_61164, c_61228])).
% 23.01/12.00  tff(c_61422, plain, (![B_8765, A_8766]: (k1_relat_1(B_8765)=A_8766 | ~v1_partfun1(B_8765, A_8766) | ~v4_relat_1(B_8765, A_8766) | ~v1_relat_1(B_8765))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_61429, plain, (![C_19, A_8735]: (k1_relat_1(C_19)=A_8735 | ~v1_partfun1(C_19, A_8735) | ~v1_relat_1(C_19) | ~m1_subset_1(C_19, '#skF_4'))), inference(resolution, [status(thm)], [c_61237, c_61422])).
% 23.01/12.00  tff(c_61712, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~m1_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_61708, c_61429])).
% 23.01/12.00  tff(c_61721, plain, (u1_struct_0('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_61163, c_220, c_61712])).
% 23.01/12.00  tff(c_61729, plain, (~v1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_61721, c_56976])).
% 23.01/12.00  tff(c_62511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62448, c_61729])).
% 23.01/12.00  tff(c_62513, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_61822])).
% 23.01/12.00  tff(c_62534, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62513, c_61729])).
% 23.01/12.00  tff(c_62542, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61139, c_61169, c_62534])).
% 23.01/12.00  tff(c_62543, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_62582, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_62543, c_144])).
% 23.01/12.00  tff(c_62588, plain, (m1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_62582, c_40388])).
% 23.01/12.00  tff(c_62544, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_179])).
% 23.01/12.00  tff(c_62592, plain, (![A_92]: (A_92='#skF_4' | ~v1_xboole_0(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_144])).
% 23.01/12.00  tff(c_62779, plain, (k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))='#skF_4'), inference(resolution, [status(thm)], [c_62544, c_62592])).
% 23.01/12.00  tff(c_62846, plain, (![B_8883, A_8884]: (B_8883='#skF_4' | A_8884='#skF_4' | k2_zfmisc_1(A_8884, B_8883)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_62582, c_62582, c_6])).
% 23.01/12.00  tff(c_62856, plain, (u1_struct_0('#skF_2')='#skF_4' | u1_struct_0('#skF_1')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_62779, c_62846])).
% 23.01/12.00  tff(c_62861, plain, (u1_struct_0('#skF_1')='#skF_4'), inference(splitLeft, [status(thm)], [c_62856])).
% 23.01/12.00  tff(c_62863, plain, (v1_funct_2('#skF_4', '#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_62861, c_107])).
% 23.01/12.00  tff(c_62589, plain, (k1_zfmisc_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_62582, c_40375])).
% 23.01/12.00  tff(c_63117, plain, (![C_8925, B_8926]: (v1_partfun1(C_8925, '#skF_4') | ~v1_funct_2(C_8925, '#skF_4', B_8926) | ~m1_subset_1(C_8925, '#skF_4') | ~v1_funct_1(C_8925))), inference(demodulation, [status(thm), theory('equality')], [c_62589, c_62582, c_62582, c_62582, c_113])).
% 23.01/12.00  tff(c_63120, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_62863, c_63117])).
% 23.01/12.00  tff(c_63123, plain, (v1_partfun1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62588, c_63120])).
% 23.01/12.00  tff(c_62593, plain, (![A_7]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_20])).
% 23.01/12.00  tff(c_62660, plain, (![C_8856, A_8857, B_8858]: (v4_relat_1(C_8856, A_8857) | ~m1_subset_1(C_8856, k1_zfmisc_1(k2_zfmisc_1(A_8857, B_8858))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 23.01/12.00  tff(c_62669, plain, (![A_8857]: (v4_relat_1('#skF_4', A_8857))), inference(resolution, [status(thm)], [c_62593, c_62660])).
% 23.01/12.00  tff(c_63019, plain, (![B_8907, A_8908]: (k1_relat_1(B_8907)=A_8908 | ~v1_partfun1(B_8907, A_8908) | ~v4_relat_1(B_8907, A_8908) | ~v1_relat_1(B_8907))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_63028, plain, (![A_8857]: (k1_relat_1('#skF_4')=A_8857 | ~v1_partfun1('#skF_4', A_8857) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62669, c_63019])).
% 23.01/12.00  tff(c_63033, plain, (![A_8857]: (k1_relat_1('#skF_4')=A_8857 | ~v1_partfun1('#skF_4', A_8857))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_63028])).
% 23.01/12.00  tff(c_63127, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_63123, c_63033])).
% 23.01/12.00  tff(c_63062, plain, (![A_8913, B_8914, C_8915]: (k1_relset_1(A_8913, B_8914, C_8915)=k1_relat_1(C_8915) | ~m1_subset_1(C_8915, k1_zfmisc_1(k2_zfmisc_1(A_8913, B_8914))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_63079, plain, (![A_8913, B_8914]: (k1_relset_1(A_8913, B_8914, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_63062])).
% 23.01/12.00  tff(c_63128, plain, (![A_8913, B_8914]: (k1_relset_1(A_8913, B_8914, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63127, c_63079])).
% 23.01/12.00  tff(c_76301, plain, (![C_11991, A_11992, B_11993]: (v1_funct_2(C_11991, A_11992, B_11993) | k1_relset_1(A_11992, B_11993, C_11991)!=A_11992 | ~m1_subset_1(C_11991, k1_zfmisc_1(k2_zfmisc_1(A_11992, B_11993))) | ~v1_funct_1(C_11991))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_76311, plain, (![A_11992, B_11993]: (v1_funct_2('#skF_4', A_11992, B_11993) | k1_relset_1(A_11992, B_11993, '#skF_4')!=A_11992 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_76301])).
% 23.01/12.00  tff(c_76367, plain, (![B_11993]: (v1_funct_2('#skF_4', '#skF_4', B_11993))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63128, c_76311])).
% 23.01/12.00  tff(c_76320, plain, (![A_11992, B_11993]: (v1_funct_2('#skF_4', A_11992, B_11993) | A_11992!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63128, c_76311])).
% 23.01/12.00  tff(c_62594, plain, (![B_4]: (k2_zfmisc_1('#skF_4', B_4)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_62582, c_10])).
% 23.01/12.00  tff(c_76636, plain, (![D_12018, A_12019, B_12020]: (v5_pre_topc(D_12018, A_12019, g1_pre_topc(u1_struct_0(B_12020), u1_pre_topc(B_12020))) | ~v5_pre_topc(D_12018, A_12019, B_12020) | ~m1_subset_1(D_12018, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12019), u1_struct_0(g1_pre_topc(u1_struct_0(B_12020), u1_pre_topc(B_12020)))))) | ~v1_funct_2(D_12018, u1_struct_0(A_12019), u1_struct_0(g1_pre_topc(u1_struct_0(B_12020), u1_pre_topc(B_12020)))) | ~m1_subset_1(D_12018, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12019), u1_struct_0(B_12020)))) | ~v1_funct_2(D_12018, u1_struct_0(A_12019), u1_struct_0(B_12020)) | ~v1_funct_1(D_12018) | ~l1_pre_topc(B_12020) | ~v2_pre_topc(B_12020) | ~l1_pre_topc(A_12019) | ~v2_pre_topc(A_12019))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_76651, plain, (![D_12018, B_12020]: (v5_pre_topc(D_12018, '#skF_1', g1_pre_topc(u1_struct_0(B_12020), u1_pre_topc(B_12020))) | ~v5_pre_topc(D_12018, '#skF_1', B_12020) | ~m1_subset_1(D_12018, k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_12020), u1_pre_topc(B_12020)))))) | ~v1_funct_2(D_12018, u1_struct_0('#skF_1'), u1_struct_0(g1_pre_topc(u1_struct_0(B_12020), u1_pre_topc(B_12020)))) | ~m1_subset_1(D_12018, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_12020)))) | ~v1_funct_2(D_12018, u1_struct_0('#skF_1'), u1_struct_0(B_12020)) | ~v1_funct_1(D_12018) | ~l1_pre_topc(B_12020) | ~v2_pre_topc(B_12020) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62861, c_76636])).
% 23.01/12.00  tff(c_77695, plain, (![D_12135, B_12136]: (v5_pre_topc(D_12135, '#skF_1', g1_pre_topc(u1_struct_0(B_12136), u1_pre_topc(B_12136))) | ~v5_pre_topc(D_12135, '#skF_1', B_12136) | ~v1_funct_2(D_12135, '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_12136), u1_pre_topc(B_12136)))) | ~m1_subset_1(D_12135, '#skF_4') | ~v1_funct_2(D_12135, '#skF_4', u1_struct_0(B_12136)) | ~v1_funct_1(D_12135) | ~l1_pre_topc(B_12136) | ~v2_pre_topc(B_12136))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_62861, c_62589, c_62594, c_62861, c_62861, c_62589, c_62594, c_76651])).
% 23.01/12.00  tff(c_77707, plain, (![B_12136]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_12136), u1_pre_topc(B_12136))) | ~v5_pre_topc('#skF_4', '#skF_1', B_12136) | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_12136)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_12136) | ~v2_pre_topc(B_12136))), inference(resolution, [status(thm)], [c_76320, c_77695])).
% 23.01/12.00  tff(c_77733, plain, (![B_12137]: (v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0(B_12137), u1_pre_topc(B_12137))) | ~v5_pre_topc('#skF_4', '#skF_1', B_12137) | ~l1_pre_topc(B_12137) | ~v2_pre_topc(B_12137))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_76367, c_62588, c_77707])).
% 23.01/12.00  tff(c_63355, plain, (![C_8950, A_8951, B_8952]: (v1_funct_2(C_8950, A_8951, B_8952) | k1_relset_1(A_8951, B_8952, C_8950)!=A_8951 | ~m1_subset_1(C_8950, k1_zfmisc_1(k2_zfmisc_1(A_8951, B_8952))) | ~v1_funct_1(C_8950))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_63365, plain, (![A_8951, B_8952]: (v1_funct_2('#skF_4', A_8951, B_8952) | k1_relset_1(A_8951, B_8952, '#skF_4')!=A_8951 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_63355])).
% 23.01/12.00  tff(c_63376, plain, (![B_8952]: (v1_funct_2('#skF_4', '#skF_4', B_8952))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63128, c_63365])).
% 23.01/12.00  tff(c_63374, plain, (![A_8951, B_8952]: (v1_funct_2('#skF_4', A_8951, B_8952) | A_8951!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63128, c_63365])).
% 23.01/12.00  tff(c_63453, plain, (![C_8963, A_8964, B_8965]: (~v1_xboole_0(C_8963) | ~v1_funct_2(C_8963, A_8964, B_8965) | ~v1_funct_1(C_8963) | ~m1_subset_1(C_8963, k1_zfmisc_1(k2_zfmisc_1(A_8964, B_8965))) | v1_xboole_0(B_8965) | v1_xboole_0(A_8964))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_63463, plain, (![A_8964, B_8965]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_8964, B_8965) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_8965) | v1_xboole_0(A_8964))), inference(resolution, [status(thm)], [c_62593, c_63453])).
% 23.01/12.00  tff(c_63474, plain, (![A_8966, B_8967]: (~v1_funct_2('#skF_4', A_8966, B_8967) | v1_xboole_0(B_8967) | v1_xboole_0(A_8966))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62543, c_63463])).
% 23.01/12.00  tff(c_63481, plain, (![B_8952, A_8951]: (v1_xboole_0(B_8952) | v1_xboole_0(A_8951) | A_8951!='#skF_4')), inference(resolution, [status(thm)], [c_63374, c_63474])).
% 23.01/12.00  tff(c_63485, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_63481])).
% 23.01/12.00  tff(c_62595, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_62582, c_8])).
% 23.01/12.00  tff(c_62875, plain, (m1_subset_1(u1_pre_topc('#skF_1'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_62861, c_64])).
% 23.01/12.00  tff(c_62883, plain, (m1_subset_1(u1_pre_topc('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_62589, c_62589, c_62875])).
% 23.01/12.00  tff(c_62585, plain, (![B_10]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_40393])).
% 23.01/12.00  tff(c_62900, plain, (v1_xboole_0(u1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_62883, c_62585])).
% 23.01/12.00  tff(c_62913, plain, (u1_pre_topc('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_62900, c_62592])).
% 23.01/12.00  tff(c_62864, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62861, c_82])).
% 23.01/12.00  tff(c_62918, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62913, c_62864])).
% 23.01/12.00  tff(c_63158, plain, (![C_8929, A_8930, B_8931]: (v1_partfun1(C_8929, A_8930) | ~v1_funct_2(C_8929, A_8930, B_8931) | ~v1_funct_1(C_8929) | ~m1_subset_1(C_8929, k1_zfmisc_1(k2_zfmisc_1(A_8930, B_8931))) | v1_xboole_0(B_8931))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_63168, plain, (![A_8930, B_8931]: (v1_partfun1('#skF_4', A_8930) | ~v1_funct_2('#skF_4', A_8930, B_8931) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_8931))), inference(resolution, [status(thm)], [c_62593, c_63158])).
% 23.01/12.00  tff(c_63204, plain, (![A_8935, B_8936]: (v1_partfun1('#skF_4', A_8935) | ~v1_funct_2('#skF_4', A_8935, B_8936) | v1_xboole_0(B_8936))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_63168])).
% 23.01/12.00  tff(c_63211, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_62918, c_63204])).
% 23.01/12.00  tff(c_63291, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_63211])).
% 23.01/12.00  tff(c_63306, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))='#skF_4'), inference(resolution, [status(thm)], [c_63291, c_62592])).
% 23.01/12.00  tff(c_63593, plain, (![D_8978, A_8979, B_8980]: (v5_pre_topc(D_8978, A_8979, g1_pre_topc(u1_struct_0(B_8980), u1_pre_topc(B_8980))) | ~v5_pre_topc(D_8978, A_8979, B_8980) | ~m1_subset_1(D_8978, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8979), u1_struct_0(g1_pre_topc(u1_struct_0(B_8980), u1_pre_topc(B_8980)))))) | ~v1_funct_2(D_8978, u1_struct_0(A_8979), u1_struct_0(g1_pre_topc(u1_struct_0(B_8980), u1_pre_topc(B_8980)))) | ~m1_subset_1(D_8978, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8979), u1_struct_0(B_8980)))) | ~v1_funct_2(D_8978, u1_struct_0(A_8979), u1_struct_0(B_8980)) | ~v1_funct_1(D_8978) | ~l1_pre_topc(B_8980) | ~v2_pre_topc(B_8980) | ~l1_pre_topc(A_8979) | ~v2_pre_topc(A_8979))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_64461, plain, (![B_9057, A_9058, B_9059]: (v5_pre_topc(B_9057, A_9058, g1_pre_topc(u1_struct_0(B_9059), u1_pre_topc(B_9059))) | ~v5_pre_topc(B_9057, A_9058, B_9059) | ~v1_funct_2(B_9057, u1_struct_0(A_9058), u1_struct_0(g1_pre_topc(u1_struct_0(B_9059), u1_pre_topc(B_9059)))) | ~m1_subset_1(B_9057, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058), u1_struct_0(B_9059)))) | ~v1_funct_2(B_9057, u1_struct_0(A_9058), u1_struct_0(B_9059)) | ~v1_funct_1(B_9057) | ~l1_pre_topc(B_9059) | ~v2_pre_topc(B_9059) | ~l1_pre_topc(A_9058) | ~v2_pre_topc(A_9058) | ~v1_xboole_0(B_9057) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058), u1_struct_0(g1_pre_topc(u1_struct_0(B_9059), u1_pre_topc(B_9059)))))))), inference(resolution, [status(thm)], [c_16, c_63593])).
% 23.01/12.00  tff(c_64472, plain, (![B_9057, A_9058]: (v5_pre_topc(B_9057, A_9058, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(B_9057, A_9058, '#skF_2') | ~v1_funct_2(B_9057, u1_struct_0(A_9058), '#skF_4') | ~m1_subset_1(B_9057, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058), u1_struct_0('#skF_2')))) | ~v1_funct_2(B_9057, u1_struct_0(A_9058), u1_struct_0('#skF_2')) | ~v1_funct_1(B_9057) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_9058) | ~v2_pre_topc(A_9058) | ~v1_xboole_0(B_9057) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9058), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))))), inference(superposition, [status(thm), theory('equality')], [c_63306, c_64461])).
% 23.01/12.00  tff(c_64541, plain, (![B_9068, A_9069]: (v5_pre_topc(B_9068, A_9069, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(B_9068, A_9069, '#skF_2') | ~v1_funct_2(B_9068, u1_struct_0(A_9069), '#skF_4') | ~m1_subset_1(B_9068, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9069), u1_struct_0('#skF_2')))) | ~v1_funct_2(B_9068, u1_struct_0(A_9069), u1_struct_0('#skF_2')) | ~v1_funct_1(B_9068) | ~l1_pre_topc(A_9069) | ~v2_pre_topc(A_9069) | ~v1_xboole_0(B_9068))), inference(demodulation, [status(thm), theory('equality')], [c_63485, c_62589, c_62595, c_63306, c_94, c_92, c_64472])).
% 23.01/12.00  tff(c_64551, plain, (![A_9069]: (v5_pre_topc('#skF_4', A_9069, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_9069, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_9069), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_9069), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_9069) | ~v2_pre_topc(A_9069) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_64541])).
% 23.01/12.00  tff(c_64562, plain, (![A_9069]: (v5_pre_topc('#skF_4', A_9069, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', A_9069, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(A_9069), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_9069), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_9069) | ~v2_pre_topc(A_9069))), inference(demodulation, [status(thm), theory('equality')], [c_63485, c_84, c_64551])).
% 23.01/12.00  tff(c_62973, plain, (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_62913, c_62861, c_56926])).
% 23.01/12.00  tff(c_63327, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_63306, c_56959])).
% 23.01/12.00  tff(c_63762, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_63327])).
% 23.01/12.00  tff(c_63768, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56959, c_63762])).
% 23.01/12.00  tff(c_63773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_63768])).
% 23.01/12.00  tff(c_63775, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_63327])).
% 23.01/12.00  tff(c_63947, plain, (![D_9013, A_9014, B_9015]: (v5_pre_topc(D_9013, g1_pre_topc(u1_struct_0(A_9014), u1_pre_topc(A_9014)), B_9015) | ~v5_pre_topc(D_9013, A_9014, B_9015) | ~m1_subset_1(D_9013, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_9014), u1_pre_topc(A_9014))), u1_struct_0(B_9015)))) | ~v1_funct_2(D_9013, u1_struct_0(g1_pre_topc(u1_struct_0(A_9014), u1_pre_topc(A_9014))), u1_struct_0(B_9015)) | ~m1_subset_1(D_9013, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9014), u1_struct_0(B_9015)))) | ~v1_funct_2(D_9013, u1_struct_0(A_9014), u1_struct_0(B_9015)) | ~v1_funct_1(D_9013) | ~l1_pre_topc(B_9015) | ~v2_pre_topc(B_9015) | ~l1_pre_topc(A_9014) | ~v2_pre_topc(A_9014))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_64789, plain, (![B_9086, A_9087, B_9088]: (v5_pre_topc(B_9086, g1_pre_topc(u1_struct_0(A_9087), u1_pre_topc(A_9087)), B_9088) | ~v5_pre_topc(B_9086, A_9087, B_9088) | ~v1_funct_2(B_9086, u1_struct_0(g1_pre_topc(u1_struct_0(A_9087), u1_pre_topc(A_9087))), u1_struct_0(B_9088)) | ~m1_subset_1(B_9086, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9087), u1_struct_0(B_9088)))) | ~v1_funct_2(B_9086, u1_struct_0(A_9087), u1_struct_0(B_9088)) | ~v1_funct_1(B_9086) | ~l1_pre_topc(B_9088) | ~v2_pre_topc(B_9088) | ~l1_pre_topc(A_9087) | ~v2_pre_topc(A_9087) | ~v1_xboole_0(B_9086) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_9087), u1_pre_topc(A_9087))), u1_struct_0(B_9088)))))), inference(resolution, [status(thm)], [c_16, c_63947])).
% 23.01/12.00  tff(c_64798, plain, (![B_9086, B_9088]: (v5_pre_topc(B_9086, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_9088) | ~v5_pre_topc(B_9086, '#skF_2', B_9088) | ~v1_funct_2(B_9086, '#skF_4', u1_struct_0(B_9088)) | ~m1_subset_1(B_9086, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_9088)))) | ~v1_funct_2(B_9086, u1_struct_0('#skF_2'), u1_struct_0(B_9088)) | ~v1_funct_1(B_9086) | ~l1_pre_topc(B_9088) | ~v2_pre_topc(B_9088) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~v1_xboole_0(B_9086) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_9088)))))), inference(superposition, [status(thm), theory('equality')], [c_63306, c_64789])).
% 23.01/12.00  tff(c_64847, plain, (![B_9094, B_9095]: (v5_pre_topc(B_9094, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_9095) | ~v5_pre_topc(B_9094, '#skF_2', B_9095) | ~v1_funct_2(B_9094, '#skF_4', u1_struct_0(B_9095)) | ~m1_subset_1(B_9094, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_9095)))) | ~v1_funct_2(B_9094, u1_struct_0('#skF_2'), u1_struct_0(B_9095)) | ~v1_funct_1(B_9094) | ~l1_pre_topc(B_9095) | ~v2_pre_topc(B_9095) | ~v1_xboole_0(B_9094))), inference(demodulation, [status(thm), theory('equality')], [c_63485, c_62589, c_62594, c_63306, c_94, c_92, c_64798])).
% 23.01/12.00  tff(c_64857, plain, (![B_9095]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_9095) | ~v5_pre_topc('#skF_4', '#skF_2', B_9095) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_9095)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_9095)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_9095) | ~v2_pre_topc(B_9095) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_64847])).
% 23.01/12.00  tff(c_64870, plain, (![B_9096]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_9096) | ~v5_pre_topc('#skF_4', '#skF_2', B_9096) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_9096)) | ~l1_pre_topc(B_9096) | ~v2_pre_topc(B_9096))), inference(demodulation, [status(thm), theory('equality')], [c_63485, c_84, c_63376, c_64857])).
% 23.01/12.00  tff(c_63794, plain, (![D_9007, A_9008, B_9009]: (v5_pre_topc(D_9007, A_9008, B_9009) | ~v5_pre_topc(D_9007, A_9008, g1_pre_topc(u1_struct_0(B_9009), u1_pre_topc(B_9009))) | ~m1_subset_1(D_9007, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9008), u1_struct_0(g1_pre_topc(u1_struct_0(B_9009), u1_pre_topc(B_9009)))))) | ~v1_funct_2(D_9007, u1_struct_0(A_9008), u1_struct_0(g1_pre_topc(u1_struct_0(B_9009), u1_pre_topc(B_9009)))) | ~m1_subset_1(D_9007, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9008), u1_struct_0(B_9009)))) | ~v1_funct_2(D_9007, u1_struct_0(A_9008), u1_struct_0(B_9009)) | ~v1_funct_1(D_9007) | ~l1_pre_topc(B_9009) | ~v2_pre_topc(B_9009) | ~l1_pre_topc(A_9008) | ~v2_pre_topc(A_9008))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_64685, plain, (![B_9077, A_9078, B_9079]: (v5_pre_topc(B_9077, A_9078, B_9079) | ~v5_pre_topc(B_9077, A_9078, g1_pre_topc(u1_struct_0(B_9079), u1_pre_topc(B_9079))) | ~v1_funct_2(B_9077, u1_struct_0(A_9078), u1_struct_0(g1_pre_topc(u1_struct_0(B_9079), u1_pre_topc(B_9079)))) | ~m1_subset_1(B_9077, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078), u1_struct_0(B_9079)))) | ~v1_funct_2(B_9077, u1_struct_0(A_9078), u1_struct_0(B_9079)) | ~v1_funct_1(B_9077) | ~l1_pre_topc(B_9079) | ~v2_pre_topc(B_9079) | ~l1_pre_topc(A_9078) | ~v2_pre_topc(A_9078) | ~v1_xboole_0(B_9077) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078), u1_struct_0(g1_pre_topc(u1_struct_0(B_9079), u1_pre_topc(B_9079)))))))), inference(resolution, [status(thm)], [c_16, c_63794])).
% 23.01/12.00  tff(c_64696, plain, (![B_9077, A_9078]: (v5_pre_topc(B_9077, A_9078, '#skF_2') | ~v5_pre_topc(B_9077, A_9078, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(B_9077, u1_struct_0(A_9078), '#skF_4') | ~m1_subset_1(B_9077, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078), u1_struct_0('#skF_2')))) | ~v1_funct_2(B_9077, u1_struct_0(A_9078), u1_struct_0('#skF_2')) | ~v1_funct_1(B_9077) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_9078) | ~v2_pre_topc(A_9078) | ~v1_xboole_0(B_9077) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9078), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))))))), inference(superposition, [status(thm), theory('equality')], [c_63306, c_64685])).
% 23.01/12.00  tff(c_64740, plain, (![B_9081, A_9082]: (v5_pre_topc(B_9081, A_9082, '#skF_2') | ~v5_pre_topc(B_9081, A_9082, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2(B_9081, u1_struct_0(A_9082), '#skF_4') | ~m1_subset_1(B_9081, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9082), u1_struct_0('#skF_2')))) | ~v1_funct_2(B_9081, u1_struct_0(A_9082), u1_struct_0('#skF_2')) | ~v1_funct_1(B_9081) | ~l1_pre_topc(A_9082) | ~v2_pre_topc(A_9082) | ~v1_xboole_0(B_9081))), inference(demodulation, [status(thm), theory('equality')], [c_63485, c_62589, c_62595, c_63306, c_94, c_92, c_64696])).
% 23.01/12.00  tff(c_64750, plain, (![A_9082]: (v5_pre_topc('#skF_4', A_9082, '#skF_2') | ~v5_pre_topc('#skF_4', A_9082, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_9082), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_9082), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_9082) | ~v2_pre_topc(A_9082) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_64740])).
% 23.01/12.00  tff(c_64761, plain, (![A_9082]: (v5_pre_topc('#skF_4', A_9082, '#skF_2') | ~v5_pre_topc('#skF_4', A_9082, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_9082), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_9082), u1_struct_0('#skF_2')) | ~l1_pre_topc(A_9082) | ~v2_pre_topc(A_9082))), inference(demodulation, [status(thm), theory('equality')], [c_63485, c_84, c_64750])).
% 23.01/12.00  tff(c_64874, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_2')) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_64870, c_64761])).
% 23.01/12.00  tff(c_64884, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_2') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_63775, c_63306, c_63376, c_63306, c_63376, c_63306, c_64874])).
% 23.01/12.00  tff(c_64947, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_64884])).
% 23.01/12.00  tff(c_64950, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_64947])).
% 23.01/12.00  tff(c_64954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_64950])).
% 23.01/12.00  tff(c_64956, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_64884])).
% 23.01/12.00  tff(c_63310, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63306, c_62918])).
% 23.01/12.00  tff(c_63972, plain, (![A_9014, B_9015]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_9014), u1_pre_topc(A_9014)), B_9015) | ~v5_pre_topc('#skF_4', A_9014, B_9015) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_9014), u1_pre_topc(A_9014))), u1_struct_0(B_9015)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9014), u1_struct_0(B_9015)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_9014), u1_struct_0(B_9015)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_9015) | ~v2_pre_topc(B_9015) | ~l1_pre_topc(A_9014) | ~v2_pre_topc(A_9014))), inference(resolution, [status(thm)], [c_62593, c_63947])).
% 23.01/12.00  tff(c_64992, plain, (![A_9103, B_9104]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_9103), u1_pre_topc(A_9103)), B_9104) | ~v5_pre_topc('#skF_4', A_9103, B_9104) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_9103), u1_pre_topc(A_9103))), u1_struct_0(B_9104)) | ~v1_funct_2('#skF_4', u1_struct_0(A_9103), u1_struct_0(B_9104)) | ~l1_pre_topc(B_9104) | ~v2_pre_topc(B_9104) | ~l1_pre_topc(A_9103) | ~v2_pre_topc(A_9103))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62593, c_63972])).
% 23.01/12.00  tff(c_65013, plain, (![B_9104]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_9104) | ~v5_pre_topc('#skF_4', '#skF_1', B_9104) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_9104)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_9104)) | ~l1_pre_topc(B_9104) | ~v2_pre_topc(B_9104) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62861, c_64992])).
% 23.01/12.00  tff(c_65032, plain, (![B_9105]: (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), B_9105) | ~v5_pre_topc('#skF_4', '#skF_1', B_9105) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), u1_struct_0(B_9105)) | ~l1_pre_topc(B_9105) | ~v2_pre_topc(B_9105))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_63376, c_62861, c_62913, c_62861, c_62913, c_65013])).
% 23.01/12.00  tff(c_65038, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_63306, c_65032])).
% 23.01/12.00  tff(c_65044, plain, (v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64956, c_63775, c_63310, c_65038])).
% 23.01/12.00  tff(c_65045, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_62973, c_65044])).
% 23.01/12.00  tff(c_65050, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64562, c_65045])).
% 23.01/12.00  tff(c_65054, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_63376, c_62861, c_63376, c_62861, c_56927, c_65050])).
% 23.01/12.00  tff(c_65055, plain, (![B_8952]: (v1_xboole_0(B_8952))), inference(splitRight, [status(thm)], [c_63481])).
% 23.01/12.00  tff(c_65109, plain, (![B_2, A_1]: (B_2=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_65055, c_65055, c_4])).
% 23.01/12.00  tff(c_65112, plain, (![B_9107, A_9108]: (B_9107=A_9108)), inference(demodulation, [status(thm), theory('equality')], [c_65055, c_65055, c_4])).
% 23.01/12.00  tff(c_76188, plain, (![A_11968]: (~v5_pre_topc('#skF_4', g1_pre_topc('#skF_4', '#skF_4'), A_11968))), inference(superposition, [status(thm), theory('equality')], [c_65112, c_62973])).
% 23.01/12.00  tff(c_76200, plain, (![B_2, A_11968]: (~v5_pre_topc('#skF_4', B_2, A_11968))), inference(superposition, [status(thm), theory('equality')], [c_65109, c_76188])).
% 23.01/12.00  tff(c_69129, plain, (![A_1]: (A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65055, c_65055, c_4])).
% 23.01/12.00  tff(c_68073, plain, (![B_9107]: (B_9107='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65055, c_65055, c_4])).
% 23.01/12.00  tff(c_68075, plain, (v5_pre_topc('#skF_4', '#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_68073, c_56927])).
% 23.01/12.00  tff(c_69131, plain, (v5_pre_topc('#skF_4', '#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_69129, c_68075])).
% 23.01/12.00  tff(c_76228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76200, c_69131])).
% 23.01/12.00  tff(c_76229, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_63211])).
% 23.01/12.00  tff(c_63003, plain, (![B_8901, A_8902, B_8903]: (v4_relat_1(B_8901, A_8902) | ~v1_xboole_0(B_8901) | ~v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(A_8902, B_8903))))), inference(resolution, [status(thm)], [c_16, c_62660])).
% 23.01/12.00  tff(c_63007, plain, (![B_8901, A_3]: (v4_relat_1(B_8901, A_3) | ~v1_xboole_0(B_8901) | ~v1_xboole_0(k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_62595, c_63003])).
% 23.01/12.00  tff(c_63011, plain, (![B_8901, A_3]: (v4_relat_1(B_8901, A_3) | ~v1_xboole_0(B_8901))), inference(demodulation, [status(thm), theory('equality')], [c_62543, c_62589, c_63007])).
% 23.01/12.00  tff(c_63029, plain, (![B_8901, A_3]: (k1_relat_1(B_8901)=A_3 | ~v1_partfun1(B_8901, A_3) | ~v1_relat_1(B_8901) | ~v1_xboole_0(B_8901))), inference(resolution, [status(thm)], [c_63011, c_63019])).
% 23.01/12.00  tff(c_76233, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_76229, c_63029])).
% 23.01/12.00  tff(c_76239, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62543, c_220, c_63127, c_76233])).
% 23.01/12.00  tff(c_76734, plain, (![D_12033, A_12034, B_12035]: (v5_pre_topc(D_12033, g1_pre_topc(u1_struct_0(A_12034), u1_pre_topc(A_12034)), B_12035) | ~v5_pre_topc(D_12033, A_12034, B_12035) | ~m1_subset_1(D_12033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12034), u1_pre_topc(A_12034))), u1_struct_0(B_12035)))) | ~v1_funct_2(D_12033, u1_struct_0(g1_pre_topc(u1_struct_0(A_12034), u1_pre_topc(A_12034))), u1_struct_0(B_12035)) | ~m1_subset_1(D_12033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12034), u1_struct_0(B_12035)))) | ~v1_funct_2(D_12033, u1_struct_0(A_12034), u1_struct_0(B_12035)) | ~v1_funct_1(D_12033) | ~l1_pre_topc(B_12035) | ~v2_pre_topc(B_12035) | ~l1_pre_topc(A_12034) | ~v2_pre_topc(A_12034))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_76749, plain, (![D_12033, B_12035]: (v5_pre_topc(D_12033, g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_12035) | ~v5_pre_topc(D_12033, '#skF_1', B_12035) | ~m1_subset_1(D_12033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_1'))), u1_struct_0(B_12035)))) | ~v1_funct_2(D_12033, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_12035)) | ~m1_subset_1(D_12033, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_12035)))) | ~v1_funct_2(D_12033, u1_struct_0('#skF_1'), u1_struct_0(B_12035)) | ~v1_funct_1(D_12033) | ~l1_pre_topc(B_12035) | ~v2_pre_topc(B_12035) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_62861, c_76734])).
% 23.01/12.00  tff(c_76802, plain, (![D_12042, B_12043]: (v5_pre_topc(D_12042, g1_pre_topc('#skF_4', '#skF_4'), B_12043) | ~v5_pre_topc(D_12042, '#skF_1', B_12043) | ~m1_subset_1(D_12042, '#skF_4') | ~v1_funct_2(D_12042, '#skF_4', u1_struct_0(B_12043)) | ~v1_funct_1(D_12042) | ~l1_pre_topc(B_12043) | ~v2_pre_topc(B_12043))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_62861, c_62589, c_62594, c_62861, c_76239, c_62861, c_62913, c_62589, c_62594, c_76239, c_62913, c_62861, c_62913, c_76749])).
% 23.01/12.00  tff(c_76805, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_76802, c_62973])).
% 23.01/12.00  tff(c_76808, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_76367, c_62588, c_76805])).
% 23.01/12.00  tff(c_76921, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_76808])).
% 23.01/12.00  tff(c_76924, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_76921])).
% 23.01/12.00  tff(c_76928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_76924])).
% 23.01/12.00  tff(c_76929, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_76808])).
% 23.01/12.00  tff(c_77070, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_76929])).
% 23.01/12.00  tff(c_77736, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_77733, c_77070])).
% 23.01/12.00  tff(c_77752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_56927, c_77736])).
% 23.01/12.00  tff(c_77753, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_76929])).
% 23.01/12.00  tff(c_77760, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56959, c_77753])).
% 23.01/12.00  tff(c_77765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_77760])).
% 23.01/12.00  tff(c_77766, plain, (u1_struct_0('#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_62856])).
% 23.01/12.00  tff(c_77769, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_77766, c_107])).
% 23.01/12.00  tff(c_77946, plain, (![A_12161, B_12162, C_12163]: (k1_relset_1(A_12161, B_12162, C_12163)=k1_relat_1(C_12163) | ~m1_subset_1(C_12163, k1_zfmisc_1(k2_zfmisc_1(A_12161, B_12162))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 23.01/12.00  tff(c_77963, plain, (![A_12161, B_12162]: (k1_relset_1(A_12161, B_12162, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_77946])).
% 23.01/12.00  tff(c_80357, plain, (![C_12955, A_12956, B_12957]: (v1_funct_2(C_12955, A_12956, B_12957) | k1_relset_1(A_12956, B_12957, C_12955)!=A_12956 | ~m1_subset_1(C_12955, k1_zfmisc_1(k2_zfmisc_1(A_12956, B_12957))) | ~v1_funct_1(C_12955))), inference(cnfTransformation, [status(thm)], [f_143])).
% 23.01/12.00  tff(c_80367, plain, (![A_12956, B_12957]: (v1_funct_2('#skF_4', A_12956, B_12957) | k1_relset_1(A_12956, B_12957, '#skF_4')!=A_12956 | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62593, c_80357])).
% 23.01/12.00  tff(c_80376, plain, (![A_12956, B_12957]: (v1_funct_2('#skF_4', A_12956, B_12957) | k1_relat_1('#skF_4')!=A_12956)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_77963, c_80367])).
% 23.01/12.00  tff(c_80439, plain, (![C_12965, A_12966, B_12967]: (~v1_xboole_0(C_12965) | ~v1_funct_2(C_12965, A_12966, B_12967) | ~v1_funct_1(C_12965) | ~m1_subset_1(C_12965, k1_zfmisc_1(k2_zfmisc_1(A_12966, B_12967))) | v1_xboole_0(B_12967) | v1_xboole_0(A_12966))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.01/12.00  tff(c_80449, plain, (![A_12966, B_12967]: (~v1_xboole_0('#skF_4') | ~v1_funct_2('#skF_4', A_12966, B_12967) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_12967) | v1_xboole_0(A_12966))), inference(resolution, [status(thm)], [c_62593, c_80439])).
% 23.01/12.00  tff(c_80460, plain, (![A_12968, B_12969]: (~v1_funct_2('#skF_4', A_12968, B_12969) | v1_xboole_0(B_12969) | v1_xboole_0(A_12968))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62543, c_80449])).
% 23.01/12.00  tff(c_80467, plain, (![B_12957, A_12956]: (v1_xboole_0(B_12957) | v1_xboole_0(A_12956) | k1_relat_1('#skF_4')!=A_12956)), inference(resolution, [status(thm)], [c_80376, c_80460])).
% 23.01/12.00  tff(c_80472, plain, (![A_12970]: (v1_xboole_0(A_12970) | k1_relat_1('#skF_4')!=A_12970)), inference(splitLeft, [status(thm)], [c_80467])).
% 23.01/12.00  tff(c_80514, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_80472, c_62592])).
% 23.01/12.00  tff(c_80380, plain, (![A_12958, B_12959]: (v1_funct_2('#skF_4', A_12958, B_12959) | k1_relat_1('#skF_4')!=A_12958)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_77963, c_80367])).
% 23.01/12.00  tff(c_78044, plain, (![C_42, B_41]: (v1_partfun1(C_42, '#skF_4') | ~v1_funct_2(C_42, '#skF_4', B_41) | ~m1_subset_1(C_42, '#skF_4') | ~v1_funct_1(C_42))), inference(demodulation, [status(thm), theory('equality')], [c_62589, c_62582, c_62582, c_62582, c_113])).
% 23.01/12.00  tff(c_80387, plain, (v1_partfun1('#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_1('#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_80380, c_78044])).
% 23.01/12.00  tff(c_80394, plain, (v1_partfun1('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62588, c_80387])).
% 23.01/12.00  tff(c_80396, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(splitLeft, [status(thm)], [c_80394])).
% 23.01/12.00  tff(c_80526, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80514, c_80396])).
% 23.01/12.00  tff(c_80527, plain, (![B_12957]: (v1_xboole_0(B_12957))), inference(splitRight, [status(thm)], [c_80467])).
% 23.01/12.00  tff(c_77781, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77766, c_64])).
% 23.01/12.00  tff(c_77789, plain, (m1_subset_1(u1_pre_topc('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_62589, c_62589, c_77781])).
% 23.01/12.00  tff(c_77800, plain, (v1_xboole_0(u1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_77789, c_62585])).
% 23.01/12.00  tff(c_77819, plain, (u1_pre_topc('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_77800, c_62592])).
% 23.01/12.00  tff(c_77770, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_77766, c_82])).
% 23.01/12.00  tff(c_77823, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_77819, c_77770])).
% 23.01/12.00  tff(c_77983, plain, (![C_12168, A_12169, B_12170]: (v1_partfun1(C_12168, A_12169) | ~v1_funct_2(C_12168, A_12169, B_12170) | ~v1_funct_1(C_12168) | ~m1_subset_1(C_12168, k1_zfmisc_1(k2_zfmisc_1(A_12169, B_12170))) | v1_xboole_0(B_12170))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.01/12.00  tff(c_77993, plain, (![A_12169, B_12170]: (v1_partfun1('#skF_4', A_12169) | ~v1_funct_2('#skF_4', A_12169, B_12170) | ~v1_funct_1('#skF_4') | v1_xboole_0(B_12170))), inference(resolution, [status(thm)], [c_62593, c_77983])).
% 23.01/12.00  tff(c_78009, plain, (![A_12173, B_12174]: (v1_partfun1('#skF_4', A_12173) | ~v1_funct_2('#skF_4', A_12173, B_12174) | v1_xboole_0(B_12174))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_77993])).
% 23.01/12.00  tff(c_78016, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(resolution, [status(thm)], [c_77823, c_78009])).
% 23.01/12.00  tff(c_78070, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitLeft, [status(thm)], [c_78016])).
% 23.01/12.00  tff(c_78085, plain, (u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_78070, c_62592])).
% 23.01/12.00  tff(c_78914, plain, (![D_12803, A_12804, B_12805]: (v5_pre_topc(D_12803, A_12804, g1_pre_topc(u1_struct_0(B_12805), u1_pre_topc(B_12805))) | ~v5_pre_topc(D_12803, A_12804, B_12805) | ~m1_subset_1(D_12803, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804), u1_struct_0(g1_pre_topc(u1_struct_0(B_12805), u1_pre_topc(B_12805)))))) | ~v1_funct_2(D_12803, u1_struct_0(A_12804), u1_struct_0(g1_pre_topc(u1_struct_0(B_12805), u1_pre_topc(B_12805)))) | ~m1_subset_1(D_12803, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804), u1_struct_0(B_12805)))) | ~v1_funct_2(D_12803, u1_struct_0(A_12804), u1_struct_0(B_12805)) | ~v1_funct_1(D_12803) | ~l1_pre_topc(B_12805) | ~v2_pre_topc(B_12805) | ~l1_pre_topc(A_12804) | ~v2_pre_topc(A_12804))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_78932, plain, (![D_12803, A_12804]: (v5_pre_topc(D_12803, A_12804, g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc(D_12803, A_12804, '#skF_2') | ~m1_subset_1(D_12803, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_2')))))) | ~v1_funct_2(D_12803, u1_struct_0(A_12804), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~m1_subset_1(D_12803, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12804), u1_struct_0('#skF_2')))) | ~v1_funct_2(D_12803, u1_struct_0(A_12804), u1_struct_0('#skF_2')) | ~v1_funct_1(D_12803) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(A_12804) | ~v2_pre_topc(A_12804))), inference(superposition, [status(thm), theory('equality')], [c_77766, c_78914])).
% 23.01/12.00  tff(c_80162, plain, (![D_12937, A_12938]: (v5_pre_topc(D_12937, A_12938, g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_12937, A_12938, '#skF_2') | ~m1_subset_1(D_12937, '#skF_4') | ~v1_funct_2(D_12937, u1_struct_0(A_12938), '#skF_4') | ~v1_funct_1(D_12937) | ~l1_pre_topc(A_12938) | ~v2_pre_topc(A_12938))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_77766, c_62589, c_62595, c_77766, c_78085, c_77766, c_77819, c_62589, c_62595, c_78085, c_77819, c_77766, c_77819, c_78932])).
% 23.01/12.00  tff(c_78089, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78085, c_77823])).
% 23.01/12.00  tff(c_77833, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), '#skF_4')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77819, c_66])).
% 23.01/12.00  tff(c_77846, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_77766, c_77833])).
% 23.01/12.00  tff(c_62587, plain, (![A_3824]: (l1_pre_topc(g1_pre_topc(A_3824, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62582, c_40369])).
% 23.01/12.00  tff(c_79181, plain, (![D_12838, A_12839, B_12840]: (v5_pre_topc(D_12838, g1_pre_topc(u1_struct_0(A_12839), u1_pre_topc(A_12839)), B_12840) | ~v5_pre_topc(D_12838, A_12839, B_12840) | ~m1_subset_1(D_12838, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12839), u1_pre_topc(A_12839))), u1_struct_0(B_12840)))) | ~v1_funct_2(D_12838, u1_struct_0(g1_pre_topc(u1_struct_0(A_12839), u1_pre_topc(A_12839))), u1_struct_0(B_12840)) | ~m1_subset_1(D_12838, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12839), u1_struct_0(B_12840)))) | ~v1_funct_2(D_12838, u1_struct_0(A_12839), u1_struct_0(B_12840)) | ~v1_funct_1(D_12838) | ~l1_pre_topc(B_12840) | ~v2_pre_topc(B_12840) | ~l1_pre_topc(A_12839) | ~v2_pre_topc(A_12839))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_79190, plain, (![D_12838, A_12839]: (v5_pre_topc(D_12838, g1_pre_topc(u1_struct_0(A_12839), u1_pre_topc(A_12839)), g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_12838, A_12839, g1_pre_topc('#skF_4', '#skF_4')) | ~m1_subset_1(D_12838, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12839), u1_pre_topc(A_12839))), '#skF_4'))) | ~v1_funct_2(D_12838, u1_struct_0(g1_pre_topc(u1_struct_0(A_12839), u1_pre_topc(A_12839))), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | ~m1_subset_1(D_12838, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12839), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))))) | ~v1_funct_2(D_12838, u1_struct_0(A_12839), u1_struct_0(g1_pre_topc('#skF_4', '#skF_4'))) | ~v1_funct_1(D_12838) | ~l1_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~l1_pre_topc(A_12839) | ~v2_pre_topc(A_12839))), inference(superposition, [status(thm), theory('equality')], [c_78085, c_79181])).
% 23.01/12.00  tff(c_79409, plain, (![D_12867, A_12868]: (v5_pre_topc(D_12867, g1_pre_topc(u1_struct_0(A_12868), u1_pre_topc(A_12868)), g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc(D_12867, A_12868, g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2(D_12867, u1_struct_0(g1_pre_topc(u1_struct_0(A_12868), u1_pre_topc(A_12868))), '#skF_4') | ~m1_subset_1(D_12867, '#skF_4') | ~v1_funct_2(D_12867, u1_struct_0(A_12868), '#skF_4') | ~v1_funct_1(D_12867) | ~l1_pre_topc(A_12868) | ~v2_pre_topc(A_12868))), inference(demodulation, [status(thm), theory('equality')], [c_77846, c_62587, c_78085, c_62589, c_62595, c_78085, c_78085, c_62589, c_62595, c_79190])).
% 23.01/12.00  tff(c_77859, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_77819, c_77766, c_56926])).
% 23.01/12.00  tff(c_79415, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), '#skF_4') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_79409, c_77859])).
% 23.01/12.00  tff(c_79431, plain, (~v5_pre_topc('#skF_4', '#skF_1', g1_pre_topc('#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_77769, c_62588, c_78089, c_79415])).
% 23.01/12.00  tff(c_80184, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80162, c_79431])).
% 23.01/12.00  tff(c_80208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84, c_77769, c_62588, c_56927, c_80184])).
% 23.01/12.00  tff(c_80210, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_4', '#skF_4')))), inference(splitRight, [status(thm)], [c_78016])).
% 23.01/12.00  tff(c_80584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80527, c_80210])).
% 23.01/12.00  tff(c_80586, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(splitRight, [status(thm)], [c_80394])).
% 23.01/12.00  tff(c_80712, plain, (![B_12957]: (v1_funct_2('#skF_4', '#skF_4', B_12957))), inference(demodulation, [status(thm), theory('equality')], [c_80586, c_80376])).
% 23.01/12.00  tff(c_80209, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(splitRight, [status(thm)], [c_78016])).
% 23.01/12.00  tff(c_77893, plain, (![B_12146, A_12147]: (k1_relat_1(B_12146)=A_12147 | ~v1_partfun1(B_12146, A_12147) | ~v4_relat_1(B_12146, A_12147) | ~v1_relat_1(B_12146))), inference(cnfTransformation, [status(thm)], [f_131])).
% 23.01/12.00  tff(c_77899, plain, (![A_8857]: (k1_relat_1('#skF_4')=A_8857 | ~v1_partfun1('#skF_4', A_8857) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_62669, c_77893])).
% 23.01/12.00  tff(c_77903, plain, (![A_8857]: (k1_relat_1('#skF_4')=A_8857 | ~v1_partfun1('#skF_4', A_8857))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_77899])).
% 23.01/12.00  tff(c_80214, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80209, c_77903])).
% 23.01/12.00  tff(c_80599, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80586, c_80214])).
% 23.01/12.00  tff(c_80898, plain, (![D_12987, A_12988, B_12989]: (v5_pre_topc(D_12987, g1_pre_topc(u1_struct_0(A_12988), u1_pre_topc(A_12988)), B_12989) | ~v5_pre_topc(D_12987, A_12988, B_12989) | ~m1_subset_1(D_12987, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12988), u1_pre_topc(A_12988))), u1_struct_0(B_12989)))) | ~v1_funct_2(D_12987, u1_struct_0(g1_pre_topc(u1_struct_0(A_12988), u1_pre_topc(A_12988))), u1_struct_0(B_12989)) | ~m1_subset_1(D_12987, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988), u1_struct_0(B_12989)))) | ~v1_funct_2(D_12987, u1_struct_0(A_12988), u1_struct_0(B_12989)) | ~v1_funct_1(D_12987) | ~l1_pre_topc(B_12989) | ~v2_pre_topc(B_12989) | ~l1_pre_topc(A_12988) | ~v2_pre_topc(A_12988))), inference(cnfTransformation, [status(thm)], [f_207])).
% 23.01/12.00  tff(c_80923, plain, (![A_12988, B_12989]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_12988), u1_pre_topc(A_12988)), B_12989) | ~v5_pre_topc('#skF_4', A_12988, B_12989) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_12988), u1_pre_topc(A_12988))), u1_struct_0(B_12989)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988), u1_struct_0(B_12989)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_12988), u1_struct_0(B_12989)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_12989) | ~v2_pre_topc(B_12989) | ~l1_pre_topc(A_12988) | ~v2_pre_topc(A_12988))), inference(resolution, [status(thm)], [c_62593, c_80898])).
% 23.01/12.00  tff(c_82575, plain, (![A_13136, B_13137]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_13136), u1_pre_topc(A_13136)), B_13137) | ~v5_pre_topc('#skF_4', A_13136, B_13137) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_13136), u1_pre_topc(A_13136))), u1_struct_0(B_13137)) | ~v1_funct_2('#skF_4', u1_struct_0(A_13136), u1_struct_0(B_13137)) | ~l1_pre_topc(B_13137) | ~v2_pre_topc(B_13137) | ~l1_pre_topc(A_13136) | ~v2_pre_topc(A_13136))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62593, c_80923])).
% 23.01/12.00  tff(c_82587, plain, (![B_13137]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_13137) | ~v5_pre_topc('#skF_4', '#skF_1', B_13137) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_13137)) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_13137)) | ~l1_pre_topc(B_13137) | ~v2_pre_topc(B_13137) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_80599, c_82575])).
% 23.01/12.00  tff(c_82606, plain, (![B_13137]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_13137) | ~v5_pre_topc('#skF_4', '#skF_1', B_13137) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0(B_13137)) | ~l1_pre_topc(B_13137) | ~v2_pre_topc(B_13137))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_80712, c_82587])).
% 23.01/12.00  tff(c_62737, plain, (![A_8864, B_8865]: (v1_pre_topc(g1_pre_topc(A_8864, B_8865)) | ~m1_subset_1(B_8865, k1_zfmisc_1(k1_zfmisc_1(A_8864))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 23.01/12.00  tff(c_62754, plain, (![A_45]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_45), u1_pre_topc(A_45))) | ~l1_pre_topc(A_45))), inference(resolution, [status(thm)], [c_64, c_62737])).
% 23.01/12.00  tff(c_80233, plain, (v1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_80214, c_62754])).
% 23.01/12.00  tff(c_80333, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_80233])).
% 23.01/12.00  tff(c_80343, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56959, c_80333])).
% 23.01/12.00  tff(c_80347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_80343])).
% 23.01/12.00  tff(c_80349, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_80233])).
% 23.01/12.00  tff(c_56961, plain, (![A_8306]: (v1_xboole_0(u1_pre_topc(A_8306)) | ~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_8306)))) | ~l1_pre_topc(A_8306))), inference(resolution, [status(thm)], [c_56949, c_18])).
% 23.01/12.00  tff(c_80679, plain, (v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))) | ~v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_80599, c_56961])).
% 23.01/12.00  tff(c_80700, plain, (v1_xboole_0(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_80349, c_62543, c_62589, c_62589, c_80679])).
% 23.01/12.00  tff(c_80757, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))='#skF_4'), inference(resolution, [status(thm)], [c_80700, c_62592])).
% 23.01/12.00  tff(c_80597, plain, (![A_12956, B_12957]: (v1_funct_2('#skF_4', A_12956, B_12957) | A_12956!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80586, c_80376])).
% 23.01/12.00  tff(c_80760, plain, (![D_12980, A_12981, B_12982]: (v5_pre_topc(D_12980, A_12981, g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982))) | ~v5_pre_topc(D_12980, A_12981, B_12982) | ~m1_subset_1(D_12980, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12981), u1_struct_0(g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982)))))) | ~v1_funct_2(D_12980, u1_struct_0(A_12981), u1_struct_0(g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982)))) | ~m1_subset_1(D_12980, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12981), u1_struct_0(B_12982)))) | ~v1_funct_2(D_12980, u1_struct_0(A_12981), u1_struct_0(B_12982)) | ~v1_funct_1(D_12980) | ~l1_pre_topc(B_12982) | ~v2_pre_topc(B_12982) | ~l1_pre_topc(A_12981) | ~v2_pre_topc(A_12981))), inference(cnfTransformation, [status(thm)], [f_236])).
% 23.01/12.00  tff(c_80775, plain, (![D_12980, B_12982]: (v5_pre_topc(D_12980, '#skF_2', g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982))) | ~v5_pre_topc(D_12980, '#skF_2', B_12982) | ~m1_subset_1(D_12980, k1_zfmisc_1(k2_zfmisc_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982)))))) | ~v1_funct_2(D_12980, u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982)))) | ~m1_subset_1(D_12980, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0(B_12982)))) | ~v1_funct_2(D_12980, u1_struct_0('#skF_2'), u1_struct_0(B_12982)) | ~v1_funct_1(D_12980) | ~l1_pre_topc(B_12982) | ~v2_pre_topc(B_12982) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_77766, c_80760])).
% 23.01/12.00  tff(c_82246, plain, (![D_13117, B_13118]: (v5_pre_topc(D_13117, '#skF_2', g1_pre_topc(u1_struct_0(B_13118), u1_pre_topc(B_13118))) | ~v5_pre_topc(D_13117, '#skF_2', B_13118) | ~v1_funct_2(D_13117, '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_13118), u1_pre_topc(B_13118)))) | ~m1_subset_1(D_13117, '#skF_4') | ~v1_funct_2(D_13117, '#skF_4', u1_struct_0(B_13118)) | ~v1_funct_1(D_13117) | ~l1_pre_topc(B_13118) | ~v2_pre_topc(B_13118))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_77766, c_62589, c_62594, c_77766, c_77766, c_62589, c_62594, c_80775])).
% 23.01/12.00  tff(c_82261, plain, (![B_13118]: (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0(B_13118), u1_pre_topc(B_13118))) | ~v5_pre_topc('#skF_4', '#skF_2', B_13118) | ~m1_subset_1('#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(B_13118)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_13118) | ~v2_pre_topc(B_13118))), inference(resolution, [status(thm)], [c_80597, c_82246])).
% 23.01/12.00  tff(c_82289, plain, (![B_13119]: (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0(B_13119), u1_pre_topc(B_13119))) | ~v5_pre_topc('#skF_4', '#skF_2', B_13119) | ~l1_pre_topc(B_13119) | ~v2_pre_topc(B_13119))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80712, c_62588, c_82261])).
% 23.01/12.00  tff(c_82295, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_80599, c_82289])).
% 23.01/12.00  tff(c_82305, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80349, c_80757, c_82295])).
% 23.01/12.00  tff(c_82311, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitLeft, [status(thm)], [c_82305])).
% 23.01/12.00  tff(c_82349, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_82311])).
% 23.01/12.00  tff(c_82353, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_82349])).
% 23.01/12.00  tff(c_82355, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')))), inference(splitRight, [status(thm)], [c_82305])).
% 23.01/12.00  tff(c_80782, plain, (![A_12981, B_12982]: (v5_pre_topc('#skF_4', A_12981, g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982))) | ~v5_pre_topc('#skF_4', A_12981, B_12982) | ~v1_funct_2('#skF_4', u1_struct_0(A_12981), u1_struct_0(g1_pre_topc(u1_struct_0(B_12982), u1_pre_topc(B_12982)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12981), u1_struct_0(B_12982)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_12981), u1_struct_0(B_12982)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_12982) | ~v2_pre_topc(B_12982) | ~l1_pre_topc(A_12981) | ~v2_pre_topc(A_12981))), inference(resolution, [status(thm)], [c_62593, c_80760])).
% 23.01/12.00  tff(c_82808, plain, (![A_13147, B_13148]: (v5_pre_topc('#skF_4', A_13147, g1_pre_topc(u1_struct_0(B_13148), u1_pre_topc(B_13148))) | ~v5_pre_topc('#skF_4', A_13147, B_13148) | ~v1_funct_2('#skF_4', u1_struct_0(A_13147), u1_struct_0(g1_pre_topc(u1_struct_0(B_13148), u1_pre_topc(B_13148)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_13147), u1_struct_0(B_13148)) | ~l1_pre_topc(B_13148) | ~v2_pre_topc(B_13148) | ~l1_pre_topc(A_13147) | ~v2_pre_topc(A_13147))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_62593, c_80782])).
% 23.01/12.00  tff(c_82817, plain, (![B_13148]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_13148), u1_pre_topc(B_13148))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_13148) | ~v1_funct_2('#skF_4', '#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(B_13148), u1_pre_topc(B_13148)))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))), u1_struct_0(B_13148)) | ~l1_pre_topc(B_13148) | ~v2_pre_topc(B_13148) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_80599, c_82808])).
% 23.01/12.00  tff(c_82848, plain, (![B_13149]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0(B_13149), u1_pre_topc(B_13149))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), B_13149) | ~l1_pre_topc(B_13149) | ~v2_pre_topc(B_13149))), inference(demodulation, [status(thm), theory('equality')], [c_82355, c_80349, c_80712, c_80599, c_80712, c_82817])).
% 23.01/12.00  tff(c_82863, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc(u1_struct_0('#skF_2'), '#skF_4')) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77819, c_82848])).
% 23.01/12.00  tff(c_82876, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), g1_pre_topc('#skF_4', '#skF_4')) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_77766, c_82863])).
% 23.01/12.00  tff(c_82877, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc('#skF_1')), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_77859, c_82876])).
% 23.01/12.00  tff(c_82886, plain, (~v5_pre_topc('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_82606, c_82877])).
% 23.01/12.00  tff(c_82899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_77769, c_77766, c_56927, c_82886])).
% 23.01/12.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.01/12.00  
% 23.01/12.00  Inference rules
% 23.01/12.00  ----------------------
% 23.01/12.00  #Ref     : 64
% 23.01/12.00  #Sup     : 15813
% 23.01/12.00  #Fact    : 0
% 23.01/12.00  #Define  : 0
% 23.01/12.00  #Split   : 501
% 23.01/12.00  #Chain   : 0
% 23.01/12.00  #Close   : 0
% 23.01/12.00  
% 23.01/12.00  Ordering : KBO
% 23.01/12.00  
% 23.01/12.00  Simplification rules
% 23.01/12.00  ----------------------
% 23.01/12.00  #Subsume      : 3647
% 23.01/12.00  #Demod        : 36334
% 23.01/12.00  #Tautology    : 6339
% 23.01/12.00  #SimpNegUnit  : 596
% 23.01/12.00  #BackRed      : 1841
% 23.01/12.00  
% 23.01/12.00  #Partial instantiations: 3024
% 23.01/12.00  #Strategies tried      : 1
% 23.01/12.00  
% 23.01/12.00  Timing (in seconds)
% 23.01/12.00  ----------------------
% 23.01/12.00  Preprocessing        : 0.43
% 23.01/12.00  Parsing              : 0.23
% 23.01/12.00  CNF conversion       : 0.03
% 23.01/12.00  Main loop            : 10.14
% 23.01/12.00  Inferencing          : 2.71
% 23.01/12.00  Reduction            : 4.29
% 23.01/12.00  Demodulation         : 3.26
% 23.01/12.00  BG Simplification    : 0.22
% 23.01/12.00  Subsumption          : 2.30
% 23.01/12.00  Abstraction          : 0.32
% 23.01/12.00  MUC search           : 0.00
% 23.01/12.00  Cooper               : 0.00
% 23.01/12.00  Total                : 11.27
% 23.01/12.00  Index Insertion      : 0.00
% 23.01/12.00  Index Deletion       : 0.00
% 23.01/12.00  Index Matching       : 0.00
% 23.01/12.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
