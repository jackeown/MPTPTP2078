%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:13 EST 2020

% Result     : Theorem 28.20s
% Output     : CNFRefutation 28.79s
% Verified   : 
% Statistics : Number of formulae       :  596 (28180 expanded)
%              Number of leaves         :   50 (9068 expanded)
%              Depth                    :   18
%              Number of atoms          : 1672 (97940 expanded)
%              Number of equality atoms :  157 (16181 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_mcart_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

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

tff(f_247,negated_conjecture,(
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

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_147,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_159,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_141,axiom,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_xboole_0(B)
     => v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

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

tff(f_217,axiom,(
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

tff(f_188,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_124,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(c_98,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_96,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_78,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_106,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_108,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_106])).

tff(c_387,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_100,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_110,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_100])).

tff(c_478,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_64,plain,(
    ! [A_49] :
      ( m1_subset_1(u1_pre_topc(A_49),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49))))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_687,plain,(
    ! [A_172,B_173] :
      ( l1_pre_topc(g1_pre_topc(A_172,B_173))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(A_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_695,plain,(
    ! [A_49] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_49),u1_pre_topc(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(resolution,[status(thm)],[c_64,c_687])).

tff(c_66,plain,(
    ! [A_50] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_50),u1_pre_topc(A_50)))
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_94,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_92,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_30,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_1'(A_21),A_21)
      | k1_xboole_0 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_86,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_111,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_86])).

tff(c_351,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_368,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_111,c_351])).

tff(c_512,plain,(
    ! [C_144,A_145,B_146] :
      ( v4_relat_1(C_144,A_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_540,plain,(
    v4_relat_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_111,c_512])).

tff(c_1255,plain,(
    ! [B_233,A_234] :
      ( k1_relat_1(B_233) = A_234
      | ~ v1_partfun1(B_233,A_234)
      | ~ v4_relat_1(B_233,A_234)
      | ~ v1_relat_1(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1267,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_540,c_1255])).

tff(c_1285,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_1267])).

tff(c_1298,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1285])).

tff(c_88,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_107,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_88])).

tff(c_1553,plain,(
    ! [B_268,C_269,A_270] :
      ( k1_xboole_0 = B_268
      | v1_partfun1(C_269,A_270)
      | ~ v1_funct_2(C_269,A_270,B_268)
      | ~ m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_268)))
      | ~ v1_funct_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1565,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_111,c_1553])).

tff(c_1584,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_1565])).

tff(c_1585,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1298,c_1584])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | ~ v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_587,plain,(
    ! [C_158,B_159,A_160] :
      ( ~ v1_xboole_0(C_158)
      | ~ m1_subset_1(B_159,k1_zfmisc_1(C_158))
      | ~ r2_hidden(A_160,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_610,plain,(
    ! [A_160] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_160,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_111,c_587])).

tff(c_744,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_610])).

tff(c_748,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_744])).

tff(c_1599,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1585,c_748])).

tff(c_1610,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1599])).

tff(c_1611,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1285])).

tff(c_1620,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_107])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_611,plain,(
    ! [A_160] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
      | ~ r2_hidden(A_160,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_587])).

tff(c_742,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_1803,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_742])).

tff(c_1807,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_6,c_1803])).

tff(c_82,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_247])).

tff(c_1622,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_82])).

tff(c_1621,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_80])).

tff(c_1820,plain,(
    ! [C_293,A_294,B_295] :
      ( v1_partfun1(C_293,A_294)
      | ~ v1_funct_2(C_293,A_294,B_295)
      | ~ v1_funct_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | v1_xboole_0(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1823,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_1621,c_1820])).

tff(c_1848,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1622,c_1823])).

tff(c_1849,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_1807,c_1848])).

tff(c_541,plain,(
    v4_relat_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_80,c_512])).

tff(c_1264,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_541,c_1255])).

tff(c_1282,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_1264])).

tff(c_2767,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1849,c_1611,c_1611,c_1282])).

tff(c_1619,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_111])).

tff(c_1613,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1611,c_387])).

tff(c_1628,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_66])).

tff(c_1643,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_1628])).

tff(c_1631,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_695])).

tff(c_1645,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1631])).

tff(c_2311,plain,(
    ! [D_332,A_333,B_334] :
      ( v5_pre_topc(D_332,A_333,B_334)
      | ~ v5_pre_topc(D_332,A_333,g1_pre_topc(u1_struct_0(B_334),u1_pre_topc(B_334)))
      | ~ m1_subset_1(D_332,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_333),u1_struct_0(g1_pre_topc(u1_struct_0(B_334),u1_pre_topc(B_334))))))
      | ~ v1_funct_2(D_332,u1_struct_0(A_333),u1_struct_0(g1_pre_topc(u1_struct_0(B_334),u1_pre_topc(B_334))))
      | ~ m1_subset_1(D_332,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_333),u1_struct_0(B_334))))
      | ~ v1_funct_2(D_332,u1_struct_0(A_333),u1_struct_0(B_334))
      | ~ v1_funct_1(D_332)
      | ~ l1_pre_topc(B_334)
      | ~ v2_pre_topc(B_334)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_2314,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1621,c_2311])).

tff(c_2331,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1643,c_1645,c_94,c_92,c_84,c_1622,c_2314])).

tff(c_3793,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_2767,c_1619,c_2767,c_1613,c_2331])).

tff(c_2843,plain,(
    ! [D_394,A_395,B_396] :
      ( v5_pre_topc(D_394,A_395,B_396)
      | ~ v5_pre_topc(D_394,g1_pre_topc(u1_struct_0(A_395),u1_pre_topc(A_395)),B_396)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_395),u1_pre_topc(A_395))),u1_struct_0(B_396))))
      | ~ v1_funct_2(D_394,u1_struct_0(g1_pre_topc(u1_struct_0(A_395),u1_pre_topc(A_395))),u1_struct_0(B_396))
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395),u1_struct_0(B_396))))
      | ~ v1_funct_2(D_394,u1_struct_0(A_395),u1_struct_0(B_396))
      | ~ v1_funct_1(D_394)
      | ~ l1_pre_topc(B_396)
      | ~ v2_pre_topc(B_396)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_2852,plain,(
    ! [D_394,B_396] :
      ( v5_pre_topc(D_394,'#skF_3',B_396)
      | ~ v5_pre_topc(D_394,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_396)
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(B_396))))
      | ~ v1_funct_2(D_394,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_396))
      | ~ m1_subset_1(D_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_396))))
      | ~ v1_funct_2(D_394,u1_struct_0('#skF_3'),u1_struct_0(B_396))
      | ~ v1_funct_1(D_394)
      | ~ l1_pre_topc(B_396)
      | ~ v2_pre_topc(B_396)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_2843])).

tff(c_17997,plain,(
    ! [D_4887,B_4888] :
      ( v5_pre_topc(D_4887,'#skF_3',B_4888)
      | ~ v5_pre_topc(D_4887,g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),B_4888)
      | ~ m1_subset_1(D_4887,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_4888))))
      | ~ v1_funct_2(D_4887,k1_relat_1('#skF_6'),u1_struct_0(B_4888))
      | ~ v1_funct_1(D_4887)
      | ~ l1_pre_topc(B_4888)
      | ~ v2_pre_topc(B_4888) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_1611,c_1611,c_2767,c_1611,c_2767,c_1611,c_2852])).

tff(c_18006,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1619,c_17997])).

tff(c_18025,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_1620,c_3793,c_18006])).

tff(c_18027,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_18025])).

tff(c_18030,plain,(
    ! [A_4889] : ~ r2_hidden(A_4889,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_18035,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_18030])).

tff(c_18063,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_2])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18060,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_6',B_5) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_18035,c_12])).

tff(c_18210,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_6,c_742])).

tff(c_18029,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_610])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18059,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_4])).

tff(c_18287,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_18029,c_18059])).

tff(c_8,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18531,plain,(
    ! [B_4925,A_4926] :
      ( B_4925 = '#skF_6'
      | A_4926 = '#skF_6'
      | k2_zfmisc_1(A_4926,B_4925) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_18035,c_18035,c_8])).

tff(c_18545,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | u1_struct_0('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_18287,c_18531])).

tff(c_18550,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_18545])).

tff(c_18568,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18550,c_82])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_18061,plain,(
    ! [A_6] : m1_subset_1('#skF_6',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_14])).

tff(c_18969,plain,(
    ! [C_4959,A_4960,B_4961] :
      ( v1_partfun1(C_4959,A_4960)
      | ~ v1_funct_2(C_4959,A_4960,B_4961)
      | ~ v1_funct_1(C_4959)
      | ~ m1_subset_1(C_4959,k1_zfmisc_1(k2_zfmisc_1(A_4960,B_4961)))
      | v1_xboole_0(B_4961) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18982,plain,(
    ! [A_4960,B_4961] :
      ( v1_partfun1('#skF_6',A_4960)
      | ~ v1_funct_2('#skF_6',A_4960,B_4961)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(B_4961) ) ),
    inference(resolution,[status(thm)],[c_18061,c_18969])).

tff(c_19738,plain,(
    ! [A_5025,B_5026] :
      ( v1_partfun1('#skF_6',A_5025)
      | ~ v1_funct_2('#skF_6',A_5025,B_5026)
      | v1_xboole_0(B_5026) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_18982])).

tff(c_19747,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_18568,c_19738])).

tff(c_19758,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_18210,c_19747])).

tff(c_154,plain,(
    ! [A_101] :
      ( v1_xboole_0(k1_relat_1(A_101))
      | ~ v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,(
    ! [A_106] :
      ( k1_relat_1(A_106) = k1_xboole_0
      | ~ v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_154,c_4])).

tff(c_173,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_165])).

tff(c_18056,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_18035,c_173])).

tff(c_542,plain,(
    ! [A_145] : v4_relat_1(k1_xboole_0,A_145) ),
    inference(resolution,[status(thm)],[c_14,c_512])).

tff(c_18044,plain,(
    ! [A_145] : v4_relat_1('#skF_6',A_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18035,c_542])).

tff(c_18551,plain,(
    ! [B_4927,A_4928] :
      ( k1_relat_1(B_4927) = A_4928
      | ~ v1_partfun1(B_4927,A_4928)
      | ~ v4_relat_1(B_4927,A_4928)
      | ~ v1_relat_1(B_4927) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_18554,plain,(
    ! [A_145] :
      ( k1_relat_1('#skF_6') = A_145
      | ~ v1_partfun1('#skF_6',A_145)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18044,c_18551])).

tff(c_18560,plain,(
    ! [A_145] :
      ( A_145 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_18056,c_18554])).

tff(c_19766,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_19758,c_18560])).

tff(c_18565,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18550,c_742])).

tff(c_19768,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19766,c_18565])).

tff(c_19773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18063,c_18060,c_19768])).

tff(c_19774,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_18545])).

tff(c_19777,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19774,c_18210])).

tff(c_19781,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19774,c_82])).

tff(c_20218,plain,(
    ! [C_5062,A_5063,B_5064] :
      ( v1_partfun1(C_5062,A_5063)
      | ~ v1_funct_2(C_5062,A_5063,B_5064)
      | ~ v1_funct_1(C_5062)
      | ~ m1_subset_1(C_5062,k1_zfmisc_1(k2_zfmisc_1(A_5063,B_5064)))
      | v1_xboole_0(B_5064) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_20231,plain,(
    ! [A_5063,B_5064] :
      ( v1_partfun1('#skF_6',A_5063)
      | ~ v1_funct_2('#skF_6',A_5063,B_5064)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(B_5064) ) ),
    inference(resolution,[status(thm)],[c_18061,c_20218])).

tff(c_21017,plain,(
    ! [A_5132,B_5133] :
      ( v1_partfun1('#skF_6',A_5132)
      | ~ v1_funct_2('#skF_6',A_5132,B_5133)
      | v1_xboole_0(B_5133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_20231])).

tff(c_21026,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_19781,c_21017])).

tff(c_21037,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_19777,c_21026])).

tff(c_19895,plain,(
    ! [B_5034,A_5035] :
      ( k1_relat_1(B_5034) = A_5035
      | ~ v1_partfun1(B_5034,A_5035)
      | ~ v4_relat_1(B_5034,A_5035)
      | ~ v1_relat_1(B_5034) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_19898,plain,(
    ! [A_145] :
      ( k1_relat_1('#skF_6') = A_145
      | ~ v1_partfun1('#skF_6',A_145)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18044,c_19895])).

tff(c_19904,plain,(
    ! [A_145] :
      ( A_145 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_18056,c_19898])).

tff(c_21045,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_21037,c_19904])).

tff(c_19778,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19774,c_742])).

tff(c_21047,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21045,c_19778])).

tff(c_21052,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18063,c_18060,c_21047])).

tff(c_21054,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_21055,plain,(
    ! [A_5134] : ~ r2_hidden(A_5134,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_21060,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_21055])).

tff(c_21084,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_4])).

tff(c_21395,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_21054,c_21084])).

tff(c_21559,plain,(
    ! [B_5172,A_5173] :
      ( B_5172 = '#skF_6'
      | A_5173 = '#skF_6'
      | k2_zfmisc_1(A_5173,B_5172) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_21060,c_8])).

tff(c_21572,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_21395,c_21559])).

tff(c_22040,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_21572])).

tff(c_22048,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22040,c_695])).

tff(c_59465,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_22048])).

tff(c_59492,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_695,c_59465])).

tff(c_59496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_59492])).

tff(c_59498,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_22048])).

tff(c_371,plain,(
    ! [A_127,B_128] : m1_subset_1('#skF_2'(A_127,B_128),k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_383,plain,(
    ! [B_5] : m1_subset_1('#skF_2'(k1_xboole_0,B_5),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_371])).

tff(c_593,plain,(
    ! [A_160,B_5] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_160,'#skF_2'(k1_xboole_0,B_5)) ) ),
    inference(resolution,[status(thm)],[c_383,c_587])).

tff(c_624,plain,(
    ! [A_166,B_167] : ~ r2_hidden(A_166,'#skF_2'(k1_xboole_0,B_167)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_593])).

tff(c_629,plain,(
    ! [B_167] : '#skF_2'(k1_xboole_0,B_167) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_624])).

tff(c_21234,plain,(
    ! [B_5143] : '#skF_2'('#skF_6',B_5143) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_629])).

tff(c_44,plain,(
    ! [A_41,B_42] : v1_funct_2('#skF_2'(A_41,B_42),A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_21242,plain,(
    ! [B_5143] : v1_funct_2('#skF_6','#skF_6',B_5143) ),
    inference(superposition,[status(thm),theory(equality)],[c_21234,c_44])).

tff(c_21065,plain,(
    ! [B_167] : '#skF_2'('#skF_6',B_167) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_629])).

tff(c_21086,plain,(
    ! [A_6] : m1_subset_1('#skF_6',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_14])).

tff(c_58,plain,(
    ! [B_45,C_46,A_44] :
      ( k1_xboole_0 = B_45
      | v1_partfun1(C_46,A_44)
      | ~ v1_funct_2(C_46,A_44,B_45)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_22102,plain,(
    ! [B_5227,C_5228,A_5229] :
      ( B_5227 = '#skF_6'
      | v1_partfun1(C_5228,A_5229)
      | ~ v1_funct_2(C_5228,A_5229,B_5227)
      | ~ m1_subset_1(C_5228,k1_zfmisc_1(k2_zfmisc_1(A_5229,B_5227)))
      | ~ v1_funct_1(C_5228) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_58])).

tff(c_22118,plain,(
    ! [B_5227,A_5229] :
      ( B_5227 = '#skF_6'
      | v1_partfun1('#skF_6',A_5229)
      | ~ v1_funct_2('#skF_6',A_5229,B_5227)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_21086,c_22102])).

tff(c_22256,plain,(
    ! [B_5238,A_5239] :
      ( B_5238 = '#skF_6'
      | v1_partfun1('#skF_6',A_5239)
      | ~ v1_funct_2('#skF_6',A_5239,B_5238) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_22118])).

tff(c_22278,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_107,c_22256])).

tff(c_22279,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_22278])).

tff(c_21081,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_173])).

tff(c_21069,plain,(
    ! [A_145] : v4_relat_1('#skF_6',A_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_542])).

tff(c_21647,plain,(
    ! [B_5177,A_5178] :
      ( k1_relat_1(B_5177) = A_5178
      | ~ v1_partfun1(B_5177,A_5178)
      | ~ v4_relat_1(B_5177,A_5178)
      | ~ v1_relat_1(B_5177) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_21650,plain,(
    ! [A_145] :
      ( k1_relat_1('#skF_6') = A_145
      | ~ v1_partfun1('#skF_6',A_145)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_21069,c_21647])).

tff(c_21656,plain,(
    ! [A_145] :
      ( A_145 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_21081,c_21650])).

tff(c_22283,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_22279,c_21656])).

tff(c_22286,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22283,c_387])).

tff(c_22285,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22283,c_22040])).

tff(c_21085,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_6',B_5) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_12])).

tff(c_46,plain,(
    ! [A_41,B_42] : v1_funct_1('#skF_2'(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    ! [A_41,B_42] : m1_subset_1('#skF_2'(A_41,B_42),k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28638,plain,(
    ! [D_5571,A_5572,B_5573] :
      ( v5_pre_topc(D_5571,A_5572,B_5573)
      | ~ v5_pre_topc(D_5571,g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572)),B_5573)
      | ~ m1_subset_1(D_5571,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573))))
      | ~ v1_funct_2(D_5571,u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573))
      | ~ m1_subset_1(D_5571,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5572),u1_struct_0(B_5573))))
      | ~ v1_funct_2(D_5571,u1_struct_0(A_5572),u1_struct_0(B_5573))
      | ~ v1_funct_1(D_5571)
      | ~ l1_pre_topc(B_5573)
      | ~ v2_pre_topc(B_5573)
      | ~ l1_pre_topc(A_5572)
      | ~ v2_pre_topc(A_5572) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_28658,plain,(
    ! [A_5572,B_5573] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573)),A_5572,B_5573)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573)),g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572)),B_5573)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573)),u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5572),u1_struct_0(B_5573))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573)),u1_struct_0(A_5572),u1_struct_0(B_5573))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572),u1_pre_topc(A_5572))),u1_struct_0(B_5573)))
      | ~ l1_pre_topc(B_5573)
      | ~ v2_pre_topc(B_5573)
      | ~ l1_pre_topc(A_5572)
      | ~ v2_pre_topc(A_5572) ) ),
    inference(resolution,[status(thm)],[c_54,c_28638])).

tff(c_29017,plain,(
    ! [A_5613,B_5614] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613),u1_pre_topc(A_5613))),u1_struct_0(B_5614)),A_5613,B_5614)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613),u1_pre_topc(A_5613))),u1_struct_0(B_5614)),g1_pre_topc(u1_struct_0(A_5613),u1_pre_topc(A_5613)),B_5614)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613),u1_pre_topc(A_5613))),u1_struct_0(B_5614)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5613),u1_struct_0(B_5614))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613),u1_pre_topc(A_5613))),u1_struct_0(B_5614)),u1_struct_0(A_5613),u1_struct_0(B_5614))
      | ~ l1_pre_topc(B_5614)
      | ~ v2_pre_topc(B_5614)
      | ~ l1_pre_topc(A_5613)
      | ~ v2_pre_topc(A_5613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_28658])).

tff(c_29025,plain,(
    ! [B_5614] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_5614)),'#skF_3',B_5614)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(B_5614)),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_5614)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_5614)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_5614))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_5614)),u1_struct_0('#skF_3'),u1_struct_0(B_5614))
      | ~ l1_pre_topc(B_5614)
      | ~ v2_pre_topc(B_5614)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22283,c_29017])).

tff(c_29044,plain,(
    ! [B_5615] :
      ( v5_pre_topc('#skF_6','#skF_3',B_5615)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_5615)
      | ~ l1_pre_topc(B_5615)
      | ~ v2_pre_topc(B_5615) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_21242,c_21065,c_22283,c_22285,c_22283,c_21086,c_21085,c_21065,c_22283,c_22285,c_22283,c_21065,c_22283,c_22285,c_21065,c_22285,c_22283,c_29025])).

tff(c_29048,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_22286,c_29044])).

tff(c_29281,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_29048])).

tff(c_29284,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_29281])).

tff(c_29288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_29284])).

tff(c_29289,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_29048])).

tff(c_29372,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_29289])).

tff(c_29375,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_695,c_29372])).

tff(c_29379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_29375])).

tff(c_29380,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_29289])).

tff(c_22561,plain,(
    ! [D_5255,A_5256,B_5257] :
      ( v5_pre_topc(D_5255,A_5256,B_5257)
      | ~ v5_pre_topc(D_5255,A_5256,g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))
      | ~ m1_subset_1(D_5255,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257))))))
      | ~ v1_funct_2(D_5255,u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257))))
      | ~ m1_subset_1(D_5255,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5256),u1_struct_0(B_5257))))
      | ~ v1_funct_2(D_5255,u1_struct_0(A_5256),u1_struct_0(B_5257))
      | ~ v1_funct_1(D_5255)
      | ~ l1_pre_topc(B_5257)
      | ~ v2_pre_topc(B_5257)
      | ~ l1_pre_topc(A_5256)
      | ~ v2_pre_topc(A_5256) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_22581,plain,(
    ! [A_5256,B_5257] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))),A_5256,B_5257)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))),A_5256,g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))),u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5256),u1_struct_0(B_5257))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))),u1_struct_0(A_5256),u1_struct_0(B_5257))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_5256),u1_struct_0(g1_pre_topc(u1_struct_0(B_5257),u1_pre_topc(B_5257)))))
      | ~ l1_pre_topc(B_5257)
      | ~ v2_pre_topc(B_5257)
      | ~ l1_pre_topc(A_5256)
      | ~ v2_pre_topc(A_5256) ) ),
    inference(resolution,[status(thm)],[c_54,c_22561])).

tff(c_29304,plain,(
    ! [A_5648,B_5649] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_5648),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),A_5648,B_5649)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_5648),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),A_5648,g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_5648),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5648),u1_struct_0(B_5649))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_5648),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),u1_struct_0(A_5648),u1_struct_0(B_5649))
      | ~ l1_pre_topc(B_5649)
      | ~ v2_pre_topc(B_5649)
      | ~ l1_pre_topc(A_5648)
      | ~ v2_pre_topc(A_5648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_22581])).

tff(c_29312,plain,(
    ! [B_5649] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),'#skF_3',B_5649)
      | ~ v5_pre_topc('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),'#skF_3',g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_5649))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_5649),u1_pre_topc(B_5649)))),u1_struct_0('#skF_3'),u1_struct_0(B_5649))
      | ~ l1_pre_topc(B_5649)
      | ~ v2_pre_topc(B_5649)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22283,c_29304])).

tff(c_32264,plain,(
    ! [B_5793] :
      ( v5_pre_topc('#skF_6','#skF_3',B_5793)
      | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_5793),u1_pre_topc(B_5793)))
      | ~ l1_pre_topc(B_5793)
      | ~ v2_pre_topc(B_5793) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_21242,c_21065,c_22283,c_22283,c_21086,c_21085,c_21065,c_22283,c_22283,c_21065,c_21065,c_22283,c_29312])).

tff(c_32273,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_29380,c_32264])).

tff(c_32285,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_32273])).

tff(c_32287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_32285])).

tff(c_32288,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_22278])).

tff(c_32290,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32288,c_387])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_21083,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_10])).

tff(c_48741,plain,(
    ! [D_8929,A_8930,B_8931] :
      ( v5_pre_topc(D_8929,A_8930,B_8931)
      | ~ v5_pre_topc(D_8929,A_8930,g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))
      | ~ m1_subset_1(D_8929,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931))))))
      | ~ v1_funct_2(D_8929,u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931))))
      | ~ m1_subset_1(D_8929,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8930),u1_struct_0(B_8931))))
      | ~ v1_funct_2(D_8929,u1_struct_0(A_8930),u1_struct_0(B_8931))
      | ~ v1_funct_1(D_8929)
      | ~ l1_pre_topc(B_8931)
      | ~ v2_pre_topc(B_8931)
      | ~ l1_pre_topc(A_8930)
      | ~ v2_pre_topc(A_8930) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_48764,plain,(
    ! [A_8930,B_8931] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))),A_8930,B_8931)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))),A_8930,g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))),u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8930),u1_struct_0(B_8931))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))),u1_struct_0(A_8930),u1_struct_0(B_8931))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_8930),u1_struct_0(g1_pre_topc(u1_struct_0(B_8931),u1_pre_topc(B_8931)))))
      | ~ l1_pre_topc(B_8931)
      | ~ v2_pre_topc(B_8931)
      | ~ l1_pre_topc(A_8930)
      | ~ v2_pre_topc(A_8930) ) ),
    inference(resolution,[status(thm)],[c_54,c_48741])).

tff(c_49096,plain,(
    ! [A_8973,B_8974] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0(B_8974),u1_pre_topc(B_8974)))),A_8973,B_8974)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0(B_8974),u1_pre_topc(B_8974)))),A_8973,g1_pre_topc(u1_struct_0(B_8974),u1_pre_topc(B_8974)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0(B_8974),u1_pre_topc(B_8974)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8973),u1_struct_0(B_8974))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0(B_8974),u1_pre_topc(B_8974)))),u1_struct_0(A_8973),u1_struct_0(B_8974))
      | ~ l1_pre_topc(B_8974)
      | ~ v2_pre_topc(B_8974)
      | ~ l1_pre_topc(A_8973)
      | ~ v2_pre_topc(A_8973) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_48764])).

tff(c_49100,plain,(
    ! [A_8973] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_8973,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),A_8973,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8973),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_8973),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_8973),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_8973)
      | ~ v2_pre_topc(A_8973) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32288,c_49096])).

tff(c_61526,plain,(
    ! [A_12695] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_12695),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),A_12695,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_12695),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),A_12695,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_12695),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_12695),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),u1_struct_0(A_12695),'#skF_6')
      | ~ l1_pre_topc(A_12695)
      | ~ v2_pre_topc(A_12695) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_32288,c_32288,c_21083,c_32288,c_32288,c_32288,c_32288,c_49100])).

tff(c_61532,plain,
    ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v5_pre_topc('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
    | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),k1_zfmisc_1('#skF_6'))
    | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_22040,c_61526])).

tff(c_61537,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59498,c_21242,c_21065,c_22040,c_22040,c_21086,c_21065,c_22040,c_32290,c_21065,c_21065,c_22040,c_61532])).

tff(c_61564,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_61537])).

tff(c_61567,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_61564])).

tff(c_61571,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_61567])).

tff(c_61572,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_61537])).

tff(c_380,plain,(
    ! [A_4] : m1_subset_1('#skF_2'(A_4,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_371])).

tff(c_591,plain,(
    ! [A_160,A_4] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_160,'#skF_2'(A_4,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_380,c_587])).

tff(c_678,plain,(
    ! [A_170,A_171] : ~ r2_hidden(A_170,'#skF_2'(A_171,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_591])).

tff(c_705,plain,(
    ! [A_175] : '#skF_2'(A_175,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_678])).

tff(c_716,plain,(
    ! [A_175] : v1_funct_2(k1_xboole_0,A_175,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_44])).

tff(c_21061,plain,(
    ! [A_175] : v1_funct_2('#skF_6',A_175,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_716])).

tff(c_686,plain,(
    ! [A_171] : '#skF_2'(A_171,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_678])).

tff(c_21062,plain,(
    ! [A_171] : '#skF_2'(A_171,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_21060,c_686])).

tff(c_32494,plain,(
    ! [D_5805,A_5806,B_5807] :
      ( v5_pre_topc(D_5805,A_5806,B_5807)
      | ~ v5_pre_topc(D_5805,g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806)),B_5807)
      | ~ m1_subset_1(D_5805,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807))))
      | ~ v1_funct_2(D_5805,u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807))
      | ~ m1_subset_1(D_5805,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5806),u1_struct_0(B_5807))))
      | ~ v1_funct_2(D_5805,u1_struct_0(A_5806),u1_struct_0(B_5807))
      | ~ v1_funct_1(D_5805)
      | ~ l1_pre_topc(B_5807)
      | ~ v2_pre_topc(B_5807)
      | ~ l1_pre_topc(A_5806)
      | ~ v2_pre_topc(A_5806) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_32517,plain,(
    ! [A_5806,B_5807] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807)),A_5806,B_5807)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807)),g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806)),B_5807)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807)),u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5806),u1_struct_0(B_5807))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807)),u1_struct_0(A_5806),u1_struct_0(B_5807))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806),u1_pre_topc(A_5806))),u1_struct_0(B_5807)))
      | ~ l1_pre_topc(B_5807)
      | ~ v2_pre_topc(B_5807)
      | ~ l1_pre_topc(A_5806)
      | ~ v2_pre_topc(A_5806) ) ),
    inference(resolution,[status(thm)],[c_54,c_32494])).

tff(c_49415,plain,(
    ! [A_9009,B_9010] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0(B_9010)),A_9009,B_9010)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0(B_9010)),g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009)),B_9010)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0(B_9010)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9009),u1_struct_0(B_9010))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0(B_9010)),u1_struct_0(A_9009),u1_struct_0(B_9010))
      | ~ l1_pre_topc(B_9010)
      | ~ v2_pre_topc(B_9010)
      | ~ l1_pre_topc(A_9009)
      | ~ v2_pre_topc(A_9009) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_32517])).

tff(c_49419,plain,(
    ! [A_9009] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0('#skF_4')),A_9009,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),'#skF_6'),g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009)),'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9009),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009))),u1_struct_0('#skF_4')),u1_struct_0(A_9009),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_9009)
      | ~ v2_pre_topc(A_9009) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32288,c_49415])).

tff(c_49433,plain,(
    ! [A_9009] :
      ( v5_pre_topc('#skF_6',A_9009,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_9009),u1_pre_topc(A_9009)),'#skF_4')
      | ~ l1_pre_topc(A_9009)
      | ~ v2_pre_topc(A_9009) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_21061,c_21062,c_32288,c_32288,c_21086,c_21083,c_21062,c_32288,c_32288,c_21062,c_21062,c_32288,c_49419])).

tff(c_61576,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_61572,c_49433])).

tff(c_61579,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_61576])).

tff(c_61581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_61579])).

tff(c_61582,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_21572])).

tff(c_61637,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61582,c_695])).

tff(c_66202,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_61637])).

tff(c_66205,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_695,c_66202])).

tff(c_66209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_66205])).

tff(c_66211,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_61637])).

tff(c_61640,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61582,c_66])).

tff(c_69010,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66211,c_61640])).

tff(c_69011,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_69010])).

tff(c_69014,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_69011])).

tff(c_69018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_69014])).

tff(c_69020,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_69010])).

tff(c_61585,plain,(
    ! [B_12699,C_12700,A_12701] :
      ( B_12699 = '#skF_6'
      | v1_partfun1(C_12700,A_12701)
      | ~ v1_funct_2(C_12700,A_12701,B_12699)
      | ~ m1_subset_1(C_12700,k1_zfmisc_1(k2_zfmisc_1(A_12701,B_12699)))
      | ~ v1_funct_1(C_12700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21060,c_58])).

tff(c_61604,plain,(
    ! [B_12699,A_12701] :
      ( B_12699 = '#skF_6'
      | v1_partfun1('#skF_6',A_12701)
      | ~ v1_funct_2('#skF_6',A_12701,B_12699)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_21086,c_61585])).

tff(c_61652,plain,(
    ! [B_12707,A_12708] :
      ( B_12707 = '#skF_6'
      | v1_partfun1('#skF_6',A_12708)
      | ~ v1_funct_2('#skF_6',A_12708,B_12707) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_61604])).

tff(c_61674,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_107,c_61652])).

tff(c_61675,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_61674])).

tff(c_61679,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_61675,c_21656])).

tff(c_61682,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61679,c_387])).

tff(c_61769,plain,(
    ! [D_12714,A_12715,B_12716] :
      ( v5_pre_topc(D_12714,A_12715,B_12716)
      | ~ v5_pre_topc(D_12714,g1_pre_topc(u1_struct_0(A_12715),u1_pre_topc(A_12715)),B_12716)
      | ~ m1_subset_1(D_12714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12715),u1_pre_topc(A_12715))),u1_struct_0(B_12716))))
      | ~ v1_funct_2(D_12714,u1_struct_0(g1_pre_topc(u1_struct_0(A_12715),u1_pre_topc(A_12715))),u1_struct_0(B_12716))
      | ~ m1_subset_1(D_12714,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12715),u1_struct_0(B_12716))))
      | ~ v1_funct_2(D_12714,u1_struct_0(A_12715),u1_struct_0(B_12716))
      | ~ v1_funct_1(D_12714)
      | ~ l1_pre_topc(B_12716)
      | ~ v2_pre_topc(B_12716)
      | ~ l1_pre_topc(A_12715)
      | ~ v2_pre_topc(A_12715) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_61788,plain,(
    ! [A_12715,B_12716] :
      ( v5_pre_topc('#skF_6',A_12715,B_12716)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_12715),u1_pre_topc(A_12715)),B_12716)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_12715),u1_pre_topc(A_12715))),u1_struct_0(B_12716))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12715),u1_struct_0(B_12716))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_12715),u1_struct_0(B_12716))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(B_12716)
      | ~ v2_pre_topc(B_12716)
      | ~ l1_pre_topc(A_12715)
      | ~ v2_pre_topc(A_12715) ) ),
    inference(resolution,[status(thm)],[c_21086,c_61769])).

tff(c_69402,plain,(
    ! [A_13199,B_13200] :
      ( v5_pre_topc('#skF_6',A_13199,B_13200)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_13199),u1_pre_topc(A_13199)),B_13200)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_13199),u1_pre_topc(A_13199))),u1_struct_0(B_13200))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_13199),u1_struct_0(B_13200))
      | ~ l1_pre_topc(B_13200)
      | ~ v2_pre_topc(B_13200)
      | ~ l1_pre_topc(A_13199)
      | ~ v2_pre_topc(A_13199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21086,c_61788])).

tff(c_69408,plain,(
    ! [B_13200] :
      ( v5_pre_topc('#skF_6','#skF_3',B_13200)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_13200)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(B_13200))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0(B_13200))
      | ~ l1_pre_topc(B_13200)
      | ~ v2_pre_topc(B_13200)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61679,c_69402])).

tff(c_69798,plain,(
    ! [B_13219] :
      ( v5_pre_topc('#skF_6','#skF_3',B_13219)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_13219)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(B_13219))
      | ~ l1_pre_topc(B_13219)
      | ~ v2_pre_topc(B_13219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_21242,c_61679,c_61679,c_69408])).

tff(c_69807,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),'#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_61582,c_69798])).

tff(c_69813,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69020,c_66211,c_21061,c_61682,c_69807])).

tff(c_66099,plain,(
    ! [D_12987,A_12988,B_12989] :
      ( v5_pre_topc(D_12987,A_12988,B_12989)
      | ~ v5_pre_topc(D_12987,A_12988,g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))
      | ~ m1_subset_1(D_12987,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989))))))
      | ~ v1_funct_2(D_12987,u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989))))
      | ~ m1_subset_1(D_12987,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988),u1_struct_0(B_12989))))
      | ~ v1_funct_2(D_12987,u1_struct_0(A_12988),u1_struct_0(B_12989))
      | ~ v1_funct_1(D_12987)
      | ~ l1_pre_topc(B_12989)
      | ~ v2_pre_topc(B_12989)
      | ~ l1_pre_topc(A_12988)
      | ~ v2_pre_topc(A_12988) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_66122,plain,(
    ! [A_12988,B_12989] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))),A_12988,B_12989)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))),A_12988,g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))),u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988),u1_struct_0(B_12989))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))),u1_struct_0(A_12988),u1_struct_0(B_12989))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_12988),u1_struct_0(g1_pre_topc(u1_struct_0(B_12989),u1_pre_topc(B_12989)))))
      | ~ l1_pre_topc(B_12989)
      | ~ v2_pre_topc(B_12989)
      | ~ l1_pre_topc(A_12988)
      | ~ v2_pre_topc(A_12988) ) ),
    inference(resolution,[status(thm)],[c_54,c_66099])).

tff(c_66652,plain,(
    ! [A_13041,B_13042] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_13041),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),A_13041,B_13042)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_13041),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),A_13041,g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_13041),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13041),u1_struct_0(B_13042))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_13041),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),u1_struct_0(A_13041),u1_struct_0(B_13042))
      | ~ l1_pre_topc(B_13042)
      | ~ v2_pre_topc(B_13042)
      | ~ l1_pre_topc(A_13041)
      | ~ v2_pre_topc(A_13041) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_66122])).

tff(c_66654,plain,(
    ! [B_13042] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),'#skF_3',B_13042)
      | ~ v5_pre_topc('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),'#skF_3',g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_13042))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))),u1_struct_0('#skF_3'),u1_struct_0(B_13042))
      | ~ l1_pre_topc(B_13042)
      | ~ v2_pre_topc(B_13042)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61679,c_66652])).

tff(c_66668,plain,(
    ! [B_13042] :
      ( v5_pre_topc('#skF_6','#skF_3',B_13042)
      | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_13042),u1_pre_topc(B_13042)))
      | ~ l1_pre_topc(B_13042)
      | ~ v2_pre_topc(B_13042) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_21242,c_21065,c_61679,c_61679,c_21086,c_21085,c_21065,c_61679,c_61679,c_21065,c_21065,c_61679,c_66654])).

tff(c_69816,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_69813,c_66668])).

tff(c_69819,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_69816])).

tff(c_69821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_69819])).

tff(c_69822,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_61674])).

tff(c_69825,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69822,c_387])).

tff(c_69824,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69822,c_61582])).

tff(c_77670,plain,(
    ! [D_13610,A_13611,B_13612] :
      ( v5_pre_topc(D_13610,A_13611,B_13612)
      | ~ v5_pre_topc(D_13610,A_13611,g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))
      | ~ m1_subset_1(D_13610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612))))))
      | ~ v1_funct_2(D_13610,u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612))))
      | ~ m1_subset_1(D_13610,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13611),u1_struct_0(B_13612))))
      | ~ v1_funct_2(D_13610,u1_struct_0(A_13611),u1_struct_0(B_13612))
      | ~ v1_funct_1(D_13610)
      | ~ l1_pre_topc(B_13612)
      | ~ v2_pre_topc(B_13612)
      | ~ l1_pre_topc(A_13611)
      | ~ v2_pre_topc(A_13611) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_77690,plain,(
    ! [A_13611,B_13612] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))),A_13611,B_13612)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))),A_13611,g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))),u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13611),u1_struct_0(B_13612))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))),u1_struct_0(A_13611),u1_struct_0(B_13612))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_13611),u1_struct_0(g1_pre_topc(u1_struct_0(B_13612),u1_pre_topc(B_13612)))))
      | ~ l1_pre_topc(B_13612)
      | ~ v2_pre_topc(B_13612)
      | ~ l1_pre_topc(A_13611)
      | ~ v2_pre_topc(A_13611) ) ),
    inference(resolution,[status(thm)],[c_54,c_77670])).

tff(c_78400,plain,(
    ! [A_13677,B_13678] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0(B_13678),u1_pre_topc(B_13678)))),A_13677,B_13678)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0(B_13678),u1_pre_topc(B_13678)))),A_13677,g1_pre_topc(u1_struct_0(B_13678),u1_pre_topc(B_13678)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0(B_13678),u1_pre_topc(B_13678)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13677),u1_struct_0(B_13678))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0(B_13678),u1_pre_topc(B_13678)))),u1_struct_0(A_13677),u1_struct_0(B_13678))
      | ~ l1_pre_topc(B_13678)
      | ~ v2_pre_topc(B_13678)
      | ~ l1_pre_topc(A_13677)
      | ~ v2_pre_topc(A_13677) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_77690])).

tff(c_78415,plain,(
    ! [A_13677] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_13677,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_13677,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13677),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_13677),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_13677),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_13677)
      | ~ v2_pre_topc(A_13677) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69822,c_78400])).

tff(c_78466,plain,(
    ! [A_13685] :
      ( v5_pre_topc('#skF_6',A_13685,'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_13685,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_13685)
      | ~ v2_pre_topc(A_13685) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_21061,c_21062,c_69822,c_69824,c_69822,c_21086,c_21083,c_21062,c_69822,c_69824,c_69822,c_21062,c_69824,c_69822,c_21062,c_69824,c_69822,c_78415])).

tff(c_78484,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_69825,c_78466])).

tff(c_78711,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_78484])).

tff(c_78714,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_78711])).

tff(c_78718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_78714])).

tff(c_78719,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78484])).

tff(c_78842,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_78719])).

tff(c_78845,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_695,c_78842])).

tff(c_78849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_78845])).

tff(c_78850,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_78719])).

tff(c_69935,plain,(
    ! [D_13225,A_13226,B_13227] :
      ( v5_pre_topc(D_13225,A_13226,B_13227)
      | ~ v5_pre_topc(D_13225,g1_pre_topc(u1_struct_0(A_13226),u1_pre_topc(A_13226)),B_13227)
      | ~ m1_subset_1(D_13225,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_13226),u1_pre_topc(A_13226))),u1_struct_0(B_13227))))
      | ~ v1_funct_2(D_13225,u1_struct_0(g1_pre_topc(u1_struct_0(A_13226),u1_pre_topc(A_13226))),u1_struct_0(B_13227))
      | ~ m1_subset_1(D_13225,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13226),u1_struct_0(B_13227))))
      | ~ v1_funct_2(D_13225,u1_struct_0(A_13226),u1_struct_0(B_13227))
      | ~ v1_funct_1(D_13225)
      | ~ l1_pre_topc(B_13227)
      | ~ v2_pre_topc(B_13227)
      | ~ l1_pre_topc(A_13226)
      | ~ v2_pre_topc(A_13226) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_69951,plain,(
    ! [A_13226,B_13227] :
      ( v5_pre_topc('#skF_6',A_13226,B_13227)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_13226),u1_pre_topc(A_13226)),B_13227)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_13226),u1_pre_topc(A_13226))),u1_struct_0(B_13227))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13226),u1_struct_0(B_13227))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_13226),u1_struct_0(B_13227))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(B_13227)
      | ~ v2_pre_topc(B_13227)
      | ~ l1_pre_topc(A_13226)
      | ~ v2_pre_topc(A_13226) ) ),
    inference(resolution,[status(thm)],[c_21086,c_69935])).

tff(c_81367,plain,(
    ! [A_13855,B_13856] :
      ( v5_pre_topc('#skF_6',A_13855,B_13856)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_13855),u1_pre_topc(A_13855)),B_13856)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_13855),u1_pre_topc(A_13855))),u1_struct_0(B_13856))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_13855),u1_struct_0(B_13856))
      | ~ l1_pre_topc(B_13856)
      | ~ v2_pre_topc(B_13856)
      | ~ l1_pre_topc(A_13855)
      | ~ v2_pre_topc(A_13855) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_21086,c_69951])).

tff(c_81382,plain,(
    ! [A_13855] :
      ( v5_pre_topc('#skF_6',A_13855,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_13855),u1_pre_topc(A_13855)),'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_13855),u1_pre_topc(A_13855))),'#skF_6')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_13855),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_13855)
      | ~ v2_pre_topc(A_13855) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69822,c_81367])).

tff(c_82427,plain,(
    ! [A_13913] :
      ( v5_pre_topc('#skF_6',A_13913,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_13913),u1_pre_topc(A_13913)),'#skF_4')
      | ~ l1_pre_topc(A_13913)
      | ~ v2_pre_topc(A_13913) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_21061,c_69822,c_21061,c_81382])).

tff(c_82436,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78850,c_82427])).

tff(c_82449,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_82436])).

tff(c_82451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_82449])).

tff(c_82452,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_82926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_387,c_82452])).

tff(c_82927,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_83184,plain,(
    ! [A_13999] :
      ( m1_subset_1(u1_pre_topc(A_13999),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13999))))
      | ~ l1_pre_topc(A_13999) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_60,plain,(
    ! [A_47,B_48] :
      ( l1_pre_topc(g1_pre_topc(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_83193,plain,(
    ! [A_13999] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_13999),u1_pre_topc(A_13999)))
      | ~ l1_pre_topc(A_13999) ) ),
    inference(resolution,[status(thm)],[c_83184,c_60])).

tff(c_83016,plain,(
    ! [C_13977,B_13978,A_13979] :
      ( ~ v1_xboole_0(C_13977)
      | ~ m1_subset_1(B_13978,k1_zfmisc_1(C_13977))
      | ~ r2_hidden(A_13979,B_13978) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_83036,plain,(
    ! [A_13979] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_13979,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_111,c_83016])).

tff(c_83243,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_83036])).

tff(c_83247,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_83243])).

tff(c_83086,plain,(
    ! [C_13984,A_13985,B_13986] :
      ( v4_relat_1(C_13984,A_13985)
      | ~ m1_subset_1(C_13984,k1_zfmisc_1(k2_zfmisc_1(A_13985,B_13986))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_83114,plain,(
    v4_relat_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_111,c_83086])).

tff(c_83768,plain,(
    ! [B_14077,A_14078] :
      ( k1_relat_1(B_14077) = A_14078
      | ~ v1_partfun1(B_14077,A_14078)
      | ~ v4_relat_1(B_14077,A_14078)
      | ~ v1_relat_1(B_14077) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_83777,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_83114,c_83768])).

tff(c_83795,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_83777])).

tff(c_84185,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_83795])).

tff(c_84385,plain,(
    ! [C_14109,A_14110,B_14111] :
      ( v1_partfun1(C_14109,A_14110)
      | ~ v1_funct_2(C_14109,A_14110,B_14111)
      | ~ v1_funct_1(C_14109)
      | ~ m1_subset_1(C_14109,k1_zfmisc_1(k2_zfmisc_1(A_14110,B_14111)))
      | v1_xboole_0(B_14111) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84397,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_111,c_84385])).

tff(c_84413,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_84397])).

tff(c_84415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83247,c_84185,c_84413])).

tff(c_84416,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_83795])).

tff(c_83015,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82927,c_110])).

tff(c_84424,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84416,c_83015])).

tff(c_83037,plain,(
    ! [A_13979] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
      | ~ r2_hidden(A_13979,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_83016])).

tff(c_83183,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_83037])).

tff(c_83506,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_6,c_83183])).

tff(c_83812,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_83795])).

tff(c_83939,plain,(
    ! [C_14088,A_14089,B_14090] :
      ( v1_partfun1(C_14088,A_14089)
      | ~ v1_funct_2(C_14088,A_14089,B_14090)
      | ~ v1_funct_1(C_14088)
      | ~ m1_subset_1(C_14088,k1_zfmisc_1(k2_zfmisc_1(A_14089,B_14090)))
      | v1_xboole_0(B_14090) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_83951,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_111,c_83939])).

tff(c_83970,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_107,c_83951])).

tff(c_83972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83247,c_83812,c_83970])).

tff(c_83973,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_83795])).

tff(c_83115,plain,(
    v4_relat_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_80,c_83086])).

tff(c_83780,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_83115,c_83768])).

tff(c_83798,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_83780])).

tff(c_83805,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_83798])).

tff(c_84084,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83973,c_83805])).

tff(c_83985,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83973,c_82])).

tff(c_83984,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83973,c_80])).

tff(c_36,plain,(
    ! [C_38,A_35,B_36] :
      ( v1_partfun1(C_38,A_35)
      | ~ v1_funct_2(C_38,A_35,B_36)
      | ~ v1_funct_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36)))
      | v1_xboole_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84158,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_83984,c_36])).

tff(c_84174,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_83985,c_84158])).

tff(c_84176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83506,c_84084,c_84174])).

tff(c_84177,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_83798])).

tff(c_84570,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84416,c_84177])).

tff(c_84428,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84416,c_82])).

tff(c_84574,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84570,c_84428])).

tff(c_84427,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84416,c_80])).

tff(c_84572,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84570,c_84427])).

tff(c_85219,plain,(
    ! [D_14161,A_14162,B_14163] :
      ( v5_pre_topc(D_14161,g1_pre_topc(u1_struct_0(A_14162),u1_pre_topc(A_14162)),B_14163)
      | ~ v5_pre_topc(D_14161,A_14162,B_14163)
      | ~ m1_subset_1(D_14161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_14162),u1_pre_topc(A_14162))),u1_struct_0(B_14163))))
      | ~ v1_funct_2(D_14161,u1_struct_0(g1_pre_topc(u1_struct_0(A_14162),u1_pre_topc(A_14162))),u1_struct_0(B_14163))
      | ~ m1_subset_1(D_14161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14162),u1_struct_0(B_14163))))
      | ~ v1_funct_2(D_14161,u1_struct_0(A_14162),u1_struct_0(B_14163))
      | ~ v1_funct_1(D_14161)
      | ~ l1_pre_topc(B_14163)
      | ~ v2_pre_topc(B_14163)
      | ~ l1_pre_topc(A_14162)
      | ~ v2_pre_topc(A_14162) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_85228,plain,(
    ! [D_14161,B_14163] :
      ( v5_pre_topc(D_14161,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_14163)
      | ~ v5_pre_topc(D_14161,'#skF_3',B_14163)
      | ~ m1_subset_1(D_14161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(B_14163))))
      | ~ v1_funct_2(D_14161,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_14163))
      | ~ m1_subset_1(D_14161,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_14163))))
      | ~ v1_funct_2(D_14161,u1_struct_0('#skF_3'),u1_struct_0(B_14163))
      | ~ v1_funct_1(D_14161)
      | ~ l1_pre_topc(B_14163)
      | ~ v2_pre_topc(B_14163)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84416,c_85219])).

tff(c_96853,plain,(
    ! [D_18816,B_18817] :
      ( v5_pre_topc(D_18816,g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),B_18817)
      | ~ v5_pre_topc(D_18816,'#skF_3',B_18817)
      | ~ m1_subset_1(D_18816,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_18817))))
      | ~ v1_funct_2(D_18816,k1_relat_1('#skF_6'),u1_struct_0(B_18817))
      | ~ v1_funct_1(D_18816)
      | ~ l1_pre_topc(B_18817)
      | ~ v2_pre_topc(B_18817) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84416,c_84416,c_84570,c_84416,c_84570,c_84416,c_85228])).

tff(c_96856,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_84572,c_96853])).

tff(c_96876,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_84574,c_96856])).

tff(c_96877,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_84424,c_96876])).

tff(c_96912,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_96877])).

tff(c_96915,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_96912])).

tff(c_96919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_96915])).

tff(c_96920,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_96877])).

tff(c_96999,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_96920])).

tff(c_84426,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84416,c_107])).

tff(c_84425,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84416,c_111])).

tff(c_85582,plain,(
    ! [D_14204,A_14205,B_14206] :
      ( v5_pre_topc(D_14204,A_14205,g1_pre_topc(u1_struct_0(B_14206),u1_pre_topc(B_14206)))
      | ~ v5_pre_topc(D_14204,A_14205,B_14206)
      | ~ m1_subset_1(D_14204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14205),u1_struct_0(g1_pre_topc(u1_struct_0(B_14206),u1_pre_topc(B_14206))))))
      | ~ v1_funct_2(D_14204,u1_struct_0(A_14205),u1_struct_0(g1_pre_topc(u1_struct_0(B_14206),u1_pre_topc(B_14206))))
      | ~ m1_subset_1(D_14204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14205),u1_struct_0(B_14206))))
      | ~ v1_funct_2(D_14204,u1_struct_0(A_14205),u1_struct_0(B_14206))
      | ~ v1_funct_1(D_14204)
      | ~ l1_pre_topc(B_14206)
      | ~ v2_pre_topc(B_14206)
      | ~ l1_pre_topc(A_14205)
      | ~ v2_pre_topc(A_14205) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_85591,plain,(
    ! [D_14204,B_14206] :
      ( v5_pre_topc(D_14204,'#skF_3',g1_pre_topc(u1_struct_0(B_14206),u1_pre_topc(B_14206)))
      | ~ v5_pre_topc(D_14204,'#skF_3',B_14206)
      | ~ m1_subset_1(D_14204,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(B_14206),u1_pre_topc(B_14206))))))
      | ~ v1_funct_2(D_14204,u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_14206),u1_pre_topc(B_14206))))
      | ~ m1_subset_1(D_14204,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_14206))))
      | ~ v1_funct_2(D_14204,u1_struct_0('#skF_3'),u1_struct_0(B_14206))
      | ~ v1_funct_1(D_14204)
      | ~ l1_pre_topc(B_14206)
      | ~ v2_pre_topc(B_14206)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84416,c_85582])).

tff(c_101815,plain,(
    ! [D_18944,B_18945] :
      ( v5_pre_topc(D_18944,'#skF_3',g1_pre_topc(u1_struct_0(B_18945),u1_pre_topc(B_18945)))
      | ~ v5_pre_topc(D_18944,'#skF_3',B_18945)
      | ~ m1_subset_1(D_18944,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(B_18945),u1_pre_topc(B_18945))))))
      | ~ v1_funct_2(D_18944,k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(B_18945),u1_pre_topc(B_18945))))
      | ~ m1_subset_1(D_18944,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_18945))))
      | ~ v1_funct_2(D_18944,k1_relat_1('#skF_6'),u1_struct_0(B_18945))
      | ~ v1_funct_1(D_18944)
      | ~ l1_pre_topc(B_18945)
      | ~ v2_pre_topc(B_18945) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_84416,c_84416,c_84416,c_85591])).

tff(c_101818,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_84572,c_101815])).

tff(c_101835,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_84,c_84426,c_84425,c_84574,c_82927,c_101818])).

tff(c_101837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96999,c_101835])).

tff(c_101838,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_96920])).

tff(c_101842,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_83193,c_101838])).

tff(c_101846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_101842])).

tff(c_101849,plain,(
    ! [A_18946] : ~ r2_hidden(A_18946,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_83036])).

tff(c_101854,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_101849])).

tff(c_101882,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_2])).

tff(c_101879,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_6',B_5) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_101854,c_12])).

tff(c_101877,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_101854,c_10])).

tff(c_101848,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_83036])).

tff(c_101878,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_4])).

tff(c_102154,plain,(
    k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_101848,c_101878])).

tff(c_102381,plain,(
    ! [B_18989,A_18990] :
      ( B_18989 = '#skF_6'
      | A_18990 = '#skF_6'
      | k2_zfmisc_1(A_18990,B_18989) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_101854,c_101854,c_8])).

tff(c_102395,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | u1_struct_0('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_102154,c_102381])).

tff(c_102400,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_102395])).

tff(c_102405,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102400,c_82])).

tff(c_101880,plain,(
    ! [A_6] : m1_subset_1('#skF_6',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_14])).

tff(c_102542,plain,(
    ! [B_18997,C_18998,A_18999] :
      ( B_18997 = '#skF_6'
      | v1_partfun1(C_18998,A_18999)
      | ~ v1_funct_2(C_18998,A_18999,B_18997)
      | ~ m1_subset_1(C_18998,k1_zfmisc_1(k2_zfmisc_1(A_18999,B_18997)))
      | ~ v1_funct_1(C_18998) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_58])).

tff(c_102552,plain,(
    ! [B_18997,A_18999] :
      ( B_18997 = '#skF_6'
      | v1_partfun1('#skF_6',A_18999)
      | ~ v1_funct_2('#skF_6',A_18999,B_18997)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_101880,c_102542])).

tff(c_102989,plain,(
    ! [B_19038,A_19039] :
      ( B_19038 = '#skF_6'
      | v1_partfun1('#skF_6',A_19039)
      | ~ v1_funct_2('#skF_6',A_19039,B_19038) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_102552])).

tff(c_103007,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_102405,c_102989])).

tff(c_103012,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_103007])).

tff(c_101875,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_101854,c_173])).

tff(c_83116,plain,(
    ! [A_13985] : v4_relat_1(k1_xboole_0,A_13985) ),
    inference(resolution,[status(thm)],[c_14,c_83086])).

tff(c_101862,plain,(
    ! [A_13985] : v4_relat_1('#skF_6',A_13985) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101854,c_83116])).

tff(c_102299,plain,(
    ! [B_18976,A_18977] :
      ( k1_relat_1(B_18976) = A_18977
      | ~ v1_partfun1(B_18976,A_18977)
      | ~ v4_relat_1(B_18976,A_18977)
      | ~ v1_relat_1(B_18976) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_102302,plain,(
    ! [A_13985] :
      ( k1_relat_1('#skF_6') = A_13985
      | ~ v1_partfun1('#skF_6',A_13985)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_101862,c_102299])).

tff(c_102308,plain,(
    ! [A_13985] :
      ( A_13985 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_13985) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_101875,c_102302])).

tff(c_103016,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_103012,c_102308])).

tff(c_102402,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102400,c_83183])).

tff(c_103018,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103016,c_102402])).

tff(c_103023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101882,c_101879,c_103018])).

tff(c_103024,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_103007])).

tff(c_103026,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103024,c_102402])).

tff(c_103031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101882,c_101877,c_103026])).

tff(c_103032,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_102395])).

tff(c_102124,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_6,c_83183])).

tff(c_103035,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103032,c_102124])).

tff(c_103039,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103032,c_82])).

tff(c_103167,plain,(
    ! [C_19045,A_19046,B_19047] :
      ( v1_partfun1(C_19045,A_19046)
      | ~ v1_funct_2(C_19045,A_19046,B_19047)
      | ~ v1_funct_1(C_19045)
      | ~ m1_subset_1(C_19045,k1_zfmisc_1(k2_zfmisc_1(A_19046,B_19047)))
      | v1_xboole_0(B_19047) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_103177,plain,(
    ! [A_19046,B_19047] :
      ( v1_partfun1('#skF_6',A_19046)
      | ~ v1_funct_2('#skF_6',A_19046,B_19047)
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(B_19047) ) ),
    inference(resolution,[status(thm)],[c_101880,c_103167])).

tff(c_103692,plain,(
    ! [A_19097,B_19098] :
      ( v1_partfun1('#skF_6',A_19097)
      | ~ v1_funct_2('#skF_6',A_19097,B_19098)
      | v1_xboole_0(B_19098) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_103177])).

tff(c_103701,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_103039,c_103692])).

tff(c_103712,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(negUnitSimplification,[status(thm)],[c_103035,c_103701])).

tff(c_103720,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_103712,c_102308])).

tff(c_103036,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103032,c_83183])).

tff(c_103723,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103720,c_103036])).

tff(c_103728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101882,c_101879,c_103723])).

tff(c_103731,plain,(
    ! [A_19099] : ~ r2_hidden(A_19099,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_83037])).

tff(c_103736,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_103731])).

tff(c_83018,plain,(
    ! [A_13979,A_4] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_13979,'#skF_2'(A_4,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_380,c_83016])).

tff(c_83121,plain,(
    ! [A_13990,A_13991] : ~ r2_hidden(A_13990,'#skF_2'(A_13991,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_83018])).

tff(c_83133,plain,(
    ! [A_13992] : '#skF_2'(A_13992,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_83121])).

tff(c_83144,plain,(
    ! [A_13992] : v1_funct_2(k1_xboole_0,A_13992,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_83133,c_44])).

tff(c_103739,plain,(
    ! [A_13992] : v1_funct_2('#skF_6',A_13992,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_83144])).

tff(c_83129,plain,(
    ! [A_13991] : '#skF_2'(A_13991,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_83121])).

tff(c_103740,plain,(
    ! [A_13991] : '#skF_2'(A_13991,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_83129])).

tff(c_83020,plain,(
    ! [A_13979,B_5] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_13979,'#skF_2'(k1_xboole_0,B_5)) ) ),
    inference(resolution,[status(thm)],[c_383,c_83016])).

tff(c_83047,plain,(
    ! [A_13981,B_13982] : ~ r2_hidden(A_13981,'#skF_2'(k1_xboole_0,B_13982)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_83020])).

tff(c_83056,plain,(
    ! [B_13983] : '#skF_2'(k1_xboole_0,B_13983) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_83047])).

tff(c_83067,plain,(
    ! [B_13983] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_13983) ),
    inference(superposition,[status(thm),theory(equality)],[c_83056,c_44])).

tff(c_103741,plain,(
    ! [B_13983] : v1_funct_2('#skF_6','#skF_6',B_13983) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_83067])).

tff(c_83052,plain,(
    ! [B_13982] : '#skF_2'(k1_xboole_0,B_13982) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_83047])).

tff(c_103744,plain,(
    ! [B_13982] : '#skF_2'('#skF_6',B_13982) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_83052])).

tff(c_103761,plain,(
    ! [A_6] : m1_subset_1('#skF_6',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_14])).

tff(c_126126,plain,(
    ! [B_20374,C_20375,A_20376] :
      ( B_20374 = '#skF_6'
      | v1_partfun1(C_20375,A_20376)
      | ~ v1_funct_2(C_20375,A_20376,B_20374)
      | ~ m1_subset_1(C_20375,k1_zfmisc_1(k2_zfmisc_1(A_20376,B_20374)))
      | ~ v1_funct_1(C_20375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_58])).

tff(c_126139,plain,(
    ! [B_20374,A_20376] :
      ( B_20374 = '#skF_6'
      | v1_partfun1('#skF_6',A_20376)
      | ~ v1_funct_2('#skF_6',A_20376,B_20374)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_103761,c_126126])).

tff(c_126280,plain,(
    ! [B_20385,A_20386] :
      ( B_20385 = '#skF_6'
      | v1_partfun1('#skF_6',A_20386)
      | ~ v1_funct_2('#skF_6',A_20386,B_20385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_126139])).

tff(c_126302,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_107,c_126280])).

tff(c_126303,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_126302])).

tff(c_103756,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_173])).

tff(c_103743,plain,(
    ! [A_13985] : v4_relat_1('#skF_6',A_13985) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_83116])).

tff(c_104394,plain,(
    ! [B_19150,A_19151] :
      ( k1_relat_1(B_19150) = A_19151
      | ~ v1_partfun1(B_19150,A_19151)
      | ~ v4_relat_1(B_19150,A_19151)
      | ~ v1_relat_1(B_19150) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_104397,plain,(
    ! [A_13985] :
      ( k1_relat_1('#skF_6') = A_13985
      | ~ v1_partfun1('#skF_6',A_13985)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_103743,c_104394])).

tff(c_104403,plain,(
    ! [A_13985] :
      ( A_13985 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_13985) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_103756,c_104397])).

tff(c_126307,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_126303,c_104403])).

tff(c_131097,plain,(
    ! [D_20667,A_20668,B_20669] :
      ( v5_pre_topc(D_20667,A_20668,g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))
      | ~ v5_pre_topc(D_20667,A_20668,B_20669)
      | ~ m1_subset_1(D_20667,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669))))))
      | ~ v1_funct_2(D_20667,u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669))))
      | ~ m1_subset_1(D_20667,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20668),u1_struct_0(B_20669))))
      | ~ v1_funct_2(D_20667,u1_struct_0(A_20668),u1_struct_0(B_20669))
      | ~ v1_funct_1(D_20667)
      | ~ l1_pre_topc(B_20669)
      | ~ v2_pre_topc(B_20669)
      | ~ l1_pre_topc(A_20668)
      | ~ v2_pre_topc(A_20668) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_131120,plain,(
    ! [A_20668,B_20669] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))),A_20668,g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))),A_20668,B_20669)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))),u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20668),u1_struct_0(B_20669))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))),u1_struct_0(A_20668),u1_struct_0(B_20669))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_20668),u1_struct_0(g1_pre_topc(u1_struct_0(B_20669),u1_pre_topc(B_20669)))))
      | ~ l1_pre_topc(B_20669)
      | ~ v2_pre_topc(B_20669)
      | ~ l1_pre_topc(A_20668)
      | ~ v2_pre_topc(A_20668) ) ),
    inference(resolution,[status(thm)],[c_54,c_131097])).

tff(c_131838,plain,(
    ! [A_20744,B_20745] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_20744),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),A_20744,g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_20744),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),A_20744,B_20745)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_20744),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20744),u1_struct_0(B_20745))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_20744),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),u1_struct_0(A_20744),u1_struct_0(B_20745))
      | ~ l1_pre_topc(B_20745)
      | ~ v2_pre_topc(B_20745)
      | ~ l1_pre_topc(A_20744)
      | ~ v2_pre_topc(A_20744) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_131120])).

tff(c_131844,plain,(
    ! [B_20745] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),'#skF_3',g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),'#skF_3',B_20745)
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0(B_20745))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))),u1_struct_0('#skF_3'),u1_struct_0(B_20745))
      | ~ l1_pre_topc(B_20745)
      | ~ v2_pre_topc(B_20745)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126307,c_131838])).

tff(c_131862,plain,(
    ! [B_20745] :
      ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_20745),u1_pre_topc(B_20745)))
      | ~ v5_pre_topc('#skF_6','#skF_3',B_20745)
      | ~ l1_pre_topc(B_20745)
      | ~ v2_pre_topc(B_20745) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_103741,c_103744,c_126307,c_126307,c_103761,c_103744,c_126307,c_103744,c_126307,c_103744,c_126307,c_131844])).

tff(c_126310,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126307,c_83015])).

tff(c_103885,plain,(
    ! [A_19110] :
      ( m1_subset_1(u1_pre_topc(A_19110),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19110))))
      | ~ l1_pre_topc(A_19110) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_103894,plain,(
    ! [A_19110] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_19110),u1_pre_topc(A_19110)))
      | ~ l1_pre_topc(A_19110) ) ),
    inference(resolution,[status(thm)],[c_103885,c_60])).

tff(c_105031,plain,(
    ! [B_19221,C_19222,A_19223] :
      ( B_19221 = '#skF_6'
      | v1_partfun1(C_19222,A_19223)
      | ~ v1_funct_2(C_19222,A_19223,B_19221)
      | ~ m1_subset_1(C_19222,k1_zfmisc_1(k2_zfmisc_1(A_19223,B_19221)))
      | ~ v1_funct_1(C_19222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_58])).

tff(c_105044,plain,(
    ! [B_19221,A_19223] :
      ( B_19221 = '#skF_6'
      | v1_partfun1('#skF_6',A_19223)
      | ~ v1_funct_2('#skF_6',A_19223,B_19221)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_103761,c_105031])).

tff(c_105195,plain,(
    ! [B_19232,A_19233] :
      ( B_19232 = '#skF_6'
      | v1_partfun1('#skF_6',A_19233)
      | ~ v1_funct_2('#skF_6',A_19233,B_19232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_105044])).

tff(c_105217,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_107,c_105195])).

tff(c_105218,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_105217])).

tff(c_105222,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_105218,c_104403])).

tff(c_105436,plain,(
    ! [D_19241,A_19242,B_19243] :
      ( v5_pre_topc(D_19241,A_19242,g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))
      | ~ v5_pre_topc(D_19241,A_19242,B_19243)
      | ~ m1_subset_1(D_19241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243))))))
      | ~ v1_funct_2(D_19241,u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243))))
      | ~ m1_subset_1(D_19241,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19242),u1_struct_0(B_19243))))
      | ~ v1_funct_2(D_19241,u1_struct_0(A_19242),u1_struct_0(B_19243))
      | ~ v1_funct_1(D_19241)
      | ~ l1_pre_topc(B_19243)
      | ~ v2_pre_topc(B_19243)
      | ~ l1_pre_topc(A_19242)
      | ~ v2_pre_topc(A_19242) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_105456,plain,(
    ! [A_19242,B_19243] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))),A_19242,g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))),A_19242,B_19243)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))),u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19242),u1_struct_0(B_19243))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))),u1_struct_0(A_19242),u1_struct_0(B_19243))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_19242),u1_struct_0(g1_pre_topc(u1_struct_0(B_19243),u1_pre_topc(B_19243)))))
      | ~ l1_pre_topc(B_19243)
      | ~ v2_pre_topc(B_19243)
      | ~ l1_pre_topc(A_19242)
      | ~ v2_pre_topc(A_19242) ) ),
    inference(resolution,[status(thm)],[c_54,c_105436])).

tff(c_112511,plain,(
    ! [A_19648,B_19649] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_19648),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),A_19648,g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_19648),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),A_19648,B_19649)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_19648),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19648),u1_struct_0(B_19649))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_19648),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),u1_struct_0(A_19648),u1_struct_0(B_19649))
      | ~ l1_pre_topc(B_19649)
      | ~ v2_pre_topc(B_19649)
      | ~ l1_pre_topc(A_19648)
      | ~ v2_pre_topc(A_19648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_105456])).

tff(c_112521,plain,(
    ! [B_19649] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),'#skF_3',g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),'#skF_3',B_19649)
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_19649))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_19649),u1_pre_topc(B_19649)))),u1_struct_0('#skF_3'),u1_struct_0(B_19649))
      | ~ l1_pre_topc(B_19649)
      | ~ v2_pre_topc(B_19649)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105222,c_112511])).

tff(c_114938,plain,(
    ! [B_19759] :
      ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_19759),u1_pre_topc(B_19759)))
      | ~ v5_pre_topc('#skF_6','#skF_3',B_19759)
      | ~ l1_pre_topc(B_19759)
      | ~ v2_pre_topc(B_19759) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_103741,c_103744,c_105222,c_105222,c_103761,c_103744,c_105222,c_103744,c_105222,c_103744,c_105222,c_112521])).

tff(c_103730,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_83037])).

tff(c_103759,plain,(
    ! [A_1] :
      ( A_1 = '#skF_6'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_4])).

tff(c_104103,plain,(
    k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_103730,c_103759])).

tff(c_104314,plain,(
    ! [B_19141,A_19142] :
      ( B_19141 = '#skF_6'
      | A_19142 = '#skF_6'
      | k2_zfmisc_1(A_19142,B_19141) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_103736,c_8])).

tff(c_104330,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_104103,c_104314])).

tff(c_104741,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_104330])).

tff(c_105224,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105222,c_104741])).

tff(c_111664,plain,(
    ! [D_19565,A_19566,B_19567] :
      ( v5_pre_topc(D_19565,g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566)),B_19567)
      | ~ v5_pre_topc(D_19565,A_19566,B_19567)
      | ~ m1_subset_1(D_19565,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567))))
      | ~ v1_funct_2(D_19565,u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567))
      | ~ m1_subset_1(D_19565,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19566),u1_struct_0(B_19567))))
      | ~ v1_funct_2(D_19565,u1_struct_0(A_19566),u1_struct_0(B_19567))
      | ~ v1_funct_1(D_19565)
      | ~ l1_pre_topc(B_19567)
      | ~ v2_pre_topc(B_19567)
      | ~ l1_pre_topc(A_19566)
      | ~ v2_pre_topc(A_19566) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_111684,plain,(
    ! [A_19566,B_19567] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567)),g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566)),B_19567)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567)),A_19566,B_19567)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567)),u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19566),u1_struct_0(B_19567))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567)),u1_struct_0(A_19566),u1_struct_0(B_19567))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566),u1_pre_topc(A_19566))),u1_struct_0(B_19567)))
      | ~ l1_pre_topc(B_19567)
      | ~ v2_pre_topc(B_19567)
      | ~ l1_pre_topc(A_19566)
      | ~ v2_pre_topc(A_19566) ) ),
    inference(resolution,[status(thm)],[c_54,c_111664])).

tff(c_112091,plain,(
    ! [A_19625,B_19626] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625),u1_pre_topc(A_19625))),u1_struct_0(B_19626)),g1_pre_topc(u1_struct_0(A_19625),u1_pre_topc(A_19625)),B_19626)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625),u1_pre_topc(A_19625))),u1_struct_0(B_19626)),A_19625,B_19626)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625),u1_pre_topc(A_19625))),u1_struct_0(B_19626)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19625),u1_struct_0(B_19626))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625),u1_pre_topc(A_19625))),u1_struct_0(B_19626)),u1_struct_0(A_19625),u1_struct_0(B_19626))
      | ~ l1_pre_topc(B_19626)
      | ~ v2_pre_topc(B_19626)
      | ~ l1_pre_topc(A_19625)
      | ~ v2_pre_topc(A_19625) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_111684])).

tff(c_112105,plain,(
    ! [B_19626] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_19626)),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_19626)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_19626)),'#skF_3',B_19626)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_19626)),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0(B_19626))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_19626)),u1_struct_0('#skF_3'),u1_struct_0(B_19626))
      | ~ l1_pre_topc(B_19626)
      | ~ v2_pre_topc(B_19626)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_105222,c_112091])).

tff(c_112232,plain,(
    ! [B_19635] :
      ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_19635)
      | ~ v5_pre_topc('#skF_6','#skF_3',B_19635)
      | ~ l1_pre_topc(B_19635)
      | ~ v2_pre_topc(B_19635) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_103741,c_103744,c_105222,c_105224,c_105222,c_103761,c_103744,c_105224,c_105222,c_103744,c_105224,c_105222,c_103744,c_105222,c_105224,c_105222,c_112105])).

tff(c_105225,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105222,c_83015])).

tff(c_112247,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_112232,c_105225])).

tff(c_112707,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_112247])).

tff(c_112710,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_112707])).

tff(c_112714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_112710])).

tff(c_112715,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_112247])).

tff(c_112812,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_112715])).

tff(c_114941,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_114938,c_112812])).

tff(c_114954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82927,c_114941])).

tff(c_114955,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_112715])).

tff(c_114959,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_103894,c_114955])).

tff(c_114963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_114959])).

tff(c_114964,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_105217])).

tff(c_103758,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_103736,c_103736,c_10])).

tff(c_122070,plain,(
    ! [D_20108,A_20109,B_20110] :
      ( v5_pre_topc(D_20108,g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109)),B_20110)
      | ~ v5_pre_topc(D_20108,A_20109,B_20110)
      | ~ m1_subset_1(D_20108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110))))
      | ~ v1_funct_2(D_20108,u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110))
      | ~ m1_subset_1(D_20108,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20109),u1_struct_0(B_20110))))
      | ~ v1_funct_2(D_20108,u1_struct_0(A_20109),u1_struct_0(B_20110))
      | ~ v1_funct_1(D_20108)
      | ~ l1_pre_topc(B_20110)
      | ~ v2_pre_topc(B_20110)
      | ~ l1_pre_topc(A_20109)
      | ~ v2_pre_topc(A_20109) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_122093,plain,(
    ! [A_20109,B_20110] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110)),g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109)),B_20110)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110)),A_20109,B_20110)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110)),u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20109),u1_struct_0(B_20110))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110)),u1_struct_0(A_20109),u1_struct_0(B_20110))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109),u1_pre_topc(A_20109))),u1_struct_0(B_20110)))
      | ~ l1_pre_topc(B_20110)
      | ~ v2_pre_topc(B_20110)
      | ~ l1_pre_topc(A_20109)
      | ~ v2_pre_topc(A_20109) ) ),
    inference(resolution,[status(thm)],[c_54,c_122070])).

tff(c_123380,plain,(
    ! [A_20214,B_20215] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0(B_20215)),g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214)),B_20215)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0(B_20215)),A_20214,B_20215)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0(B_20215)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20214),u1_struct_0(B_20215))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0(B_20215)),u1_struct_0(A_20214),u1_struct_0(B_20215))
      | ~ l1_pre_topc(B_20215)
      | ~ v2_pre_topc(B_20215)
      | ~ l1_pre_topc(A_20214)
      | ~ v2_pre_topc(A_20214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_122093])).

tff(c_123388,plain,(
    ! [A_20214] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0('#skF_4')),g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214)),'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0('#skF_4')),A_20214,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20214),'#skF_6')))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214))),u1_struct_0('#skF_4')),u1_struct_0(A_20214),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_20214)
      | ~ v2_pre_topc(A_20214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114964,c_123380])).

tff(c_123406,plain,(
    ! [A_20214] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_20214),u1_pre_topc(A_20214)),'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_20214,'#skF_4')
      | ~ l1_pre_topc(A_20214)
      | ~ v2_pre_topc(A_20214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_103739,c_103740,c_114964,c_114964,c_103761,c_103758,c_103740,c_114964,c_103740,c_114964,c_103740,c_114964,c_123388])).

tff(c_114966,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114964,c_83015])).

tff(c_115164,plain,(
    ! [D_19769,A_19770,B_19771] :
      ( v5_pre_topc(D_19769,A_19770,g1_pre_topc(u1_struct_0(B_19771),u1_pre_topc(B_19771)))
      | ~ v5_pre_topc(D_19769,A_19770,B_19771)
      | ~ m1_subset_1(D_19769,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19770),u1_struct_0(g1_pre_topc(u1_struct_0(B_19771),u1_pre_topc(B_19771))))))
      | ~ v1_funct_2(D_19769,u1_struct_0(A_19770),u1_struct_0(g1_pre_topc(u1_struct_0(B_19771),u1_pre_topc(B_19771))))
      | ~ m1_subset_1(D_19769,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19770),u1_struct_0(B_19771))))
      | ~ v1_funct_2(D_19769,u1_struct_0(A_19770),u1_struct_0(B_19771))
      | ~ v1_funct_1(D_19769)
      | ~ l1_pre_topc(B_19771)
      | ~ v2_pre_topc(B_19771)
      | ~ l1_pre_topc(A_19770)
      | ~ v2_pre_topc(A_19770) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_115183,plain,(
    ! [A_19770,B_19771] :
      ( v5_pre_topc('#skF_6',A_19770,g1_pre_topc(u1_struct_0(B_19771),u1_pre_topc(B_19771)))
      | ~ v5_pre_topc('#skF_6',A_19770,B_19771)
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_19770),u1_struct_0(g1_pre_topc(u1_struct_0(B_19771),u1_pre_topc(B_19771))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19770),u1_struct_0(B_19771))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_19770),u1_struct_0(B_19771))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(B_19771)
      | ~ v2_pre_topc(B_19771)
      | ~ l1_pre_topc(A_19770)
      | ~ v2_pre_topc(A_19770) ) ),
    inference(resolution,[status(thm)],[c_103761,c_115164])).

tff(c_125314,plain,(
    ! [A_20310,B_20311] :
      ( v5_pre_topc('#skF_6',A_20310,g1_pre_topc(u1_struct_0(B_20311),u1_pre_topc(B_20311)))
      | ~ v5_pre_topc('#skF_6',A_20310,B_20311)
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20310),u1_struct_0(g1_pre_topc(u1_struct_0(B_20311),u1_pre_topc(B_20311))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20310),u1_struct_0(B_20311))
      | ~ l1_pre_topc(B_20311)
      | ~ v2_pre_topc(B_20311)
      | ~ l1_pre_topc(A_20310)
      | ~ v2_pre_topc(A_20310) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_103761,c_115183])).

tff(c_125323,plain,(
    ! [A_20310] :
      ( v5_pre_topc('#skF_6',A_20310,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_20310,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20310),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20310),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_20310)
      | ~ v2_pre_topc(A_20310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114964,c_125314])).

tff(c_125394,plain,(
    ! [A_20314] :
      ( v5_pre_topc('#skF_6',A_20314,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_20314,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20314),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(A_20314)
      | ~ v2_pre_topc(A_20314) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_103739,c_114964,c_114964,c_125323])).

tff(c_125403,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104741,c_125394])).

tff(c_125409,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103741,c_125403])).

tff(c_125410,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_114966,c_125409])).

tff(c_125638,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_125410])).

tff(c_125641,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_125638])).

tff(c_125645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_125641])).

tff(c_125646,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_125410])).

tff(c_125901,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_125646])).

tff(c_125904,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_123406,c_125901])).

tff(c_125908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_82927,c_125904])).

tff(c_125909,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_125646])).

tff(c_125913,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_103894,c_125909])).

tff(c_125917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_125913])).

tff(c_125918,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_104330])).

tff(c_125930,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125918,c_103894])).

tff(c_131182,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_125930])).

tff(c_131240,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_103894,c_131182])).

tff(c_131244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_131240])).

tff(c_131246,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_125930])).

tff(c_62,plain,(
    ! [A_47,B_48] :
      ( v1_pre_topc(g1_pre_topc(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_103896,plain,(
    ! [A_19110] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_19110),u1_pre_topc(A_19110)))
      | ~ l1_pre_topc(A_19110) ) ),
    inference(resolution,[status(thm)],[c_103885,c_62])).

tff(c_125927,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125918,c_103896])).

tff(c_131263,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_125927])).

tff(c_131266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131246,c_131263])).

tff(c_131268,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_125927])).

tff(c_125933,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125918,c_66])).

tff(c_134127,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131268,c_125933])).

tff(c_134128,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_134127])).

tff(c_134131,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_134128])).

tff(c_134135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_134131])).

tff(c_134137,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_134127])).

tff(c_131269,plain,(
    ! [D_20683,A_20684,B_20685] :
      ( v5_pre_topc(D_20683,g1_pre_topc(u1_struct_0(A_20684),u1_pre_topc(A_20684)),B_20685)
      | ~ v5_pre_topc(D_20683,A_20684,B_20685)
      | ~ m1_subset_1(D_20683,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_20684),u1_pre_topc(A_20684))),u1_struct_0(B_20685))))
      | ~ v1_funct_2(D_20683,u1_struct_0(g1_pre_topc(u1_struct_0(A_20684),u1_pre_topc(A_20684))),u1_struct_0(B_20685))
      | ~ m1_subset_1(D_20683,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20684),u1_struct_0(B_20685))))
      | ~ v1_funct_2(D_20683,u1_struct_0(A_20684),u1_struct_0(B_20685))
      | ~ v1_funct_1(D_20683)
      | ~ l1_pre_topc(B_20685)
      | ~ v2_pre_topc(B_20685)
      | ~ l1_pre_topc(A_20684)
      | ~ v2_pre_topc(A_20684) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_131288,plain,(
    ! [A_20684,B_20685] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_20684),u1_pre_topc(A_20684)),B_20685)
      | ~ v5_pre_topc('#skF_6',A_20684,B_20685)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_20684),u1_pre_topc(A_20684))),u1_struct_0(B_20685))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20684),u1_struct_0(B_20685))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20684),u1_struct_0(B_20685))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(B_20685)
      | ~ v2_pre_topc(B_20685)
      | ~ l1_pre_topc(A_20684)
      | ~ v2_pre_topc(A_20684) ) ),
    inference(resolution,[status(thm)],[c_103761,c_131269])).

tff(c_134612,plain,(
    ! [A_20888,B_20889] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_20888),u1_pre_topc(A_20888)),B_20889)
      | ~ v5_pre_topc('#skF_6',A_20888,B_20889)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_20888),u1_pre_topc(A_20888))),u1_struct_0(B_20889))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_20888),u1_struct_0(B_20889))
      | ~ l1_pre_topc(B_20889)
      | ~ v2_pre_topc(B_20889)
      | ~ l1_pre_topc(A_20888)
      | ~ v2_pre_topc(A_20888) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_103761,c_131288])).

tff(c_134618,plain,(
    ! [B_20889] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_20889)
      | ~ v5_pre_topc('#skF_6','#skF_3',B_20889)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(B_20889))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0(B_20889))
      | ~ l1_pre_topc(B_20889)
      | ~ v2_pre_topc(B_20889)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126307,c_134612])).

tff(c_135033,plain,(
    ! [B_20924] :
      ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_20924)
      | ~ v5_pre_topc('#skF_6','#skF_3',B_20924)
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(B_20924))
      | ~ l1_pre_topc(B_20924)
      | ~ v2_pre_topc(B_20924) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_103741,c_126307,c_126307,c_134618])).

tff(c_135042,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),'#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_125918,c_135033])).

tff(c_135048,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134137,c_131268,c_103739,c_135042])).

tff(c_135049,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_126310,c_135048])).

tff(c_135052,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_131862,c_135049])).

tff(c_135056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82927,c_135052])).

tff(c_135057,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_126302])).

tff(c_135383,plain,(
    ! [D_20944,A_20945,B_20946] :
      ( v5_pre_topc(D_20944,g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945)),B_20946)
      | ~ v5_pre_topc(D_20944,A_20945,B_20946)
      | ~ m1_subset_1(D_20944,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946))))
      | ~ v1_funct_2(D_20944,u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946))
      | ~ m1_subset_1(D_20944,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20945),u1_struct_0(B_20946))))
      | ~ v1_funct_2(D_20944,u1_struct_0(A_20945),u1_struct_0(B_20946))
      | ~ v1_funct_1(D_20944)
      | ~ l1_pre_topc(B_20946)
      | ~ v2_pre_topc(B_20946)
      | ~ l1_pre_topc(A_20945)
      | ~ v2_pre_topc(A_20945) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_135403,plain,(
    ! [A_20945,B_20946] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946)),g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945)),B_20946)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946)),A_20945,B_20946)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946)),u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20945),u1_struct_0(B_20946))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946)),u1_struct_0(A_20945),u1_struct_0(B_20946))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945),u1_pre_topc(A_20945))),u1_struct_0(B_20946)))
      | ~ l1_pre_topc(B_20946)
      | ~ v2_pre_topc(B_20946)
      | ~ l1_pre_topc(A_20945)
      | ~ v2_pre_topc(A_20945) ) ),
    inference(resolution,[status(thm)],[c_54,c_135383])).

tff(c_144681,plain,(
    ! [A_22263,B_22264] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0(B_22264)),g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263)),B_22264)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0(B_22264)),A_22263,B_22264)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0(B_22264)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22263),u1_struct_0(B_22264))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0(B_22264)),u1_struct_0(A_22263),u1_struct_0(B_22264))
      | ~ l1_pre_topc(B_22264)
      | ~ v2_pre_topc(B_22264)
      | ~ l1_pre_topc(A_22263)
      | ~ v2_pre_topc(A_22263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_135403])).

tff(c_144697,plain,(
    ! [A_22263] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0('#skF_4')),g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263)),'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0('#skF_4')),A_22263,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22263),'#skF_6')))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263),u1_pre_topc(A_22263))),u1_struct_0('#skF_4')),u1_struct_0(A_22263),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_22263)
      | ~ v2_pre_topc(A_22263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135057,c_144681])).

tff(c_147729,plain,(
    ! [A_22434] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_22434),u1_pre_topc(A_22434)),'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_22434,'#skF_4')
      | ~ l1_pre_topc(A_22434)
      | ~ v2_pre_topc(A_22434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_103739,c_103740,c_135057,c_135057,c_103761,c_103758,c_103740,c_135057,c_103740,c_135057,c_103740,c_135057,c_144697])).

tff(c_135059,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135057,c_125918])).

tff(c_144323,plain,(
    ! [D_22227,A_22228,B_22229] :
      ( v5_pre_topc(D_22227,A_22228,g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))
      | ~ v5_pre_topc(D_22227,A_22228,B_22229)
      | ~ m1_subset_1(D_22227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229))))))
      | ~ v1_funct_2(D_22227,u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229))))
      | ~ m1_subset_1(D_22227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228),u1_struct_0(B_22229))))
      | ~ v1_funct_2(D_22227,u1_struct_0(A_22228),u1_struct_0(B_22229))
      | ~ v1_funct_1(D_22227)
      | ~ l1_pre_topc(B_22229)
      | ~ v2_pre_topc(B_22229)
      | ~ l1_pre_topc(A_22228)
      | ~ v2_pre_topc(A_22228) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_144335,plain,(
    ! [D_22227,A_22228] :
      ( v5_pre_topc(D_22227,A_22228,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc(D_22227,A_22228,'#skF_4')
      | ~ m1_subset_1(D_22227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2(D_22227,u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(D_22227,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_22227,u1_struct_0(A_22228),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_22227)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_22228)
      | ~ v2_pre_topc(A_22228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135057,c_144323])).

tff(c_144376,plain,(
    ! [D_22230,A_22231] :
      ( v5_pre_topc(D_22230,A_22231,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc(D_22230,A_22231,'#skF_4')
      | ~ m1_subset_1(D_22230,k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2(D_22230,u1_struct_0(A_22231),'#skF_6')
      | ~ v1_funct_1(D_22230)
      | ~ l1_pre_topc(A_22231)
      | ~ v2_pre_topc(A_22231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_135057,c_103758,c_135057,c_135059,c_135057,c_103758,c_135059,c_135057,c_144335])).

tff(c_135060,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135057,c_83015])).

tff(c_144379,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_144376,c_135060])).

tff(c_144382,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_103739,c_103761,c_144379])).

tff(c_144468,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_144382])).

tff(c_144471,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_144468])).

tff(c_144475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_144471])).

tff(c_144477,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_144382])).

tff(c_144343,plain,(
    ! [A_22228,B_22229] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))),A_22228,g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))),A_22228,B_22229)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))),u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228),u1_struct_0(B_22229))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))),u1_struct_0(A_22228),u1_struct_0(B_22229))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_22228),u1_struct_0(g1_pre_topc(u1_struct_0(B_22229),u1_pre_topc(B_22229)))))
      | ~ l1_pre_topc(B_22229)
      | ~ v2_pre_topc(B_22229)
      | ~ l1_pre_topc(A_22228)
      | ~ v2_pre_topc(A_22228) ) ),
    inference(resolution,[status(thm)],[c_54,c_144323])).

tff(c_144919,plain,(
    ! [A_22291,B_22292] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0(B_22292),u1_pre_topc(B_22292)))),A_22291,g1_pre_topc(u1_struct_0(B_22292),u1_pre_topc(B_22292)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0(B_22292),u1_pre_topc(B_22292)))),A_22291,B_22292)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0(B_22292),u1_pre_topc(B_22292)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22291),u1_struct_0(B_22292))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0(B_22292),u1_pre_topc(B_22292)))),u1_struct_0(A_22291),u1_struct_0(B_22292))
      | ~ l1_pre_topc(B_22292)
      | ~ v2_pre_topc(B_22292)
      | ~ l1_pre_topc(A_22291)
      | ~ v2_pre_topc(A_22291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_144343])).

tff(c_144935,plain,(
    ! [A_22291] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_22291,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_22291,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22291),'#skF_6')))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_22291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_22291),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_22291)
      | ~ v2_pre_topc(A_22291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135057,c_144919])).

tff(c_146805,plain,(
    ! [A_22381] :
      ( v5_pre_topc('#skF_6',A_22381,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_22381,'#skF_4')
      | ~ l1_pre_topc(A_22381)
      | ~ v2_pre_topc(A_22381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_103739,c_103740,c_135057,c_135059,c_135057,c_103761,c_103758,c_103740,c_135059,c_135057,c_103740,c_135059,c_135057,c_103740,c_135057,c_135059,c_135057,c_144935])).

tff(c_146815,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_146805,c_135060])).

tff(c_146822,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144477,c_146815])).

tff(c_146923,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_146822])).

tff(c_146926,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_103894,c_146923])).

tff(c_146930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_146926])).

tff(c_146931,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_146822])).

tff(c_147732,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_147729,c_146931])).

tff(c_147745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_82927,c_147732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:05:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 28.20/18.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.60/18.29  
% 28.60/18.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.60/18.29  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_mcart_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 28.60/18.29  
% 28.60/18.29  %Foreground sorts:
% 28.60/18.29  
% 28.60/18.29  
% 28.60/18.29  %Background operators:
% 28.60/18.29  
% 28.60/18.29  
% 28.60/18.29  %Foreground operators:
% 28.60/18.29  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 28.60/18.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 28.60/18.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 28.60/18.29  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 28.60/18.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 28.60/18.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 28.60/18.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 28.60/18.29  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 28.60/18.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 28.60/18.29  tff('#skF_5', type, '#skF_5': $i).
% 28.60/18.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 28.60/18.29  tff('#skF_6', type, '#skF_6': $i).
% 28.60/18.29  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 28.60/18.29  tff('#skF_3', type, '#skF_3': $i).
% 28.60/18.29  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 28.60/18.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 28.60/18.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 28.60/18.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 28.60/18.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 28.60/18.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 28.60/18.29  tff('#skF_4', type, '#skF_4': $i).
% 28.60/18.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 28.60/18.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 28.60/18.29  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 28.60/18.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 28.60/18.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 28.60/18.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 28.60/18.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 28.60/18.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 28.60/18.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 28.60/18.29  
% 28.79/18.35  tff(f_247, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 28.79/18.35  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 28.79/18.35  tff(f_147, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 28.79/18.35  tff(f_159, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 28.79/18.35  tff(f_89, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 28.79/18.35  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 28.79/18.35  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 28.79/18.35  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 28.79/18.35  tff(f_111, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 28.79/18.35  tff(f_141, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 28.79/18.35  tff(f_34, axiom, (![A, B]: (v1_xboole_0(B) => v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_zfmisc_1)).
% 28.79/18.35  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 28.79/18.35  tff(f_103, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 28.79/18.35  tff(f_217, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 28.79/18.35  tff(f_188, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 28.79/18.35  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 28.79/18.35  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 28.79/18.35  tff(f_42, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 28.79/18.35  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 28.79/18.35  tff(f_124, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 28.79/18.35  tff(c_98, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_96, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_78, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_106, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_108, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_106])).
% 28.79/18.35  tff(c_387, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_108])).
% 28.79/18.35  tff(c_100, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_110, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_100])).
% 28.79/18.35  tff(c_478, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_110])).
% 28.79/18.35  tff(c_64, plain, (![A_49]: (m1_subset_1(u1_pre_topc(A_49), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_49)))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_151])).
% 28.79/18.35  tff(c_687, plain, (![A_172, B_173]: (l1_pre_topc(g1_pre_topc(A_172, B_173)) | ~m1_subset_1(B_173, k1_zfmisc_1(k1_zfmisc_1(A_172))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 28.79/18.35  tff(c_695, plain, (![A_49]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_49), u1_pre_topc(A_49))) | ~l1_pre_topc(A_49))), inference(resolution, [status(thm)], [c_64, c_687])).
% 28.79/18.35  tff(c_66, plain, (![A_50]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_50), u1_pre_topc(A_50))) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_159])).
% 28.79/18.35  tff(c_94, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_92, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_30, plain, (![A_21]: (r2_hidden('#skF_1'(A_21), A_21) | k1_xboole_0=A_21)), inference(cnfTransformation, [status(thm)], [f_89])).
% 28.79/18.35  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 28.79/18.35  tff(c_86, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_111, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_86])).
% 28.79/18.35  tff(c_351, plain, (![C_124, A_125, B_126]: (v1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 28.79/18.35  tff(c_368, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_111, c_351])).
% 28.79/18.35  tff(c_512, plain, (![C_144, A_145, B_146]: (v4_relat_1(C_144, A_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 28.79/18.35  tff(c_540, plain, (v4_relat_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_111, c_512])).
% 28.79/18.35  tff(c_1255, plain, (![B_233, A_234]: (k1_relat_1(B_233)=A_234 | ~v1_partfun1(B_233, A_234) | ~v4_relat_1(B_233, A_234) | ~v1_relat_1(B_233))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.35  tff(c_1267, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_540, c_1255])).
% 28.79/18.35  tff(c_1285, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_1267])).
% 28.79/18.35  tff(c_1298, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1285])).
% 28.79/18.35  tff(c_88, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_107, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_88])).
% 28.79/18.35  tff(c_1553, plain, (![B_268, C_269, A_270]: (k1_xboole_0=B_268 | v1_partfun1(C_269, A_270) | ~v1_funct_2(C_269, A_270, B_268) | ~m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_268))) | ~v1_funct_1(C_269))), inference(cnfTransformation, [status(thm)], [f_141])).
% 28.79/18.35  tff(c_1565, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_111, c_1553])).
% 28.79/18.35  tff(c_1584, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_1565])).
% 28.79/18.35  tff(c_1585, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1298, c_1584])).
% 28.79/18.35  tff(c_6, plain, (![A_2, B_3]: (v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | ~v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 28.79/18.35  tff(c_587, plain, (![C_158, B_159, A_160]: (~v1_xboole_0(C_158) | ~m1_subset_1(B_159, k1_zfmisc_1(C_158)) | ~r2_hidden(A_160, B_159))), inference(cnfTransformation, [status(thm)], [f_55])).
% 28.79/18.35  tff(c_610, plain, (![A_160]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))) | ~r2_hidden(A_160, '#skF_6'))), inference(resolution, [status(thm)], [c_111, c_587])).
% 28.79/18.35  tff(c_744, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_610])).
% 28.79/18.35  tff(c_748, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_744])).
% 28.79/18.35  tff(c_1599, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1585, c_748])).
% 28.79/18.35  tff(c_1610, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1599])).
% 28.79/18.35  tff(c_1611, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_1285])).
% 28.79/18.35  tff(c_1620, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_107])).
% 28.79/18.35  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_611, plain, (![A_160]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~r2_hidden(A_160, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_587])).
% 28.79/18.35  tff(c_742, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitLeft, [status(thm)], [c_611])).
% 28.79/18.35  tff(c_1803, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_742])).
% 28.79/18.35  tff(c_1807, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_1803])).
% 28.79/18.35  tff(c_82, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_247])).
% 28.79/18.35  tff(c_1622, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_82])).
% 28.79/18.35  tff(c_1621, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_80])).
% 28.79/18.35  tff(c_1820, plain, (![C_293, A_294, B_295]: (v1_partfun1(C_293, A_294) | ~v1_funct_2(C_293, A_294, B_295) | ~v1_funct_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | v1_xboole_0(B_295))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.35  tff(c_1823, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_1621, c_1820])).
% 28.79/18.35  tff(c_1848, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1622, c_1823])).
% 28.79/18.35  tff(c_1849, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_1807, c_1848])).
% 28.79/18.35  tff(c_541, plain, (v4_relat_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_80, c_512])).
% 28.79/18.35  tff(c_1264, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_541, c_1255])).
% 28.79/18.35  tff(c_1282, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_1264])).
% 28.79/18.35  tff(c_2767, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1849, c_1611, c_1611, c_1282])).
% 28.79/18.35  tff(c_1619, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_111])).
% 28.79/18.35  tff(c_1613, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1611, c_387])).
% 28.79/18.35  tff(c_1628, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1611, c_66])).
% 28.79/18.35  tff(c_1643, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_1628])).
% 28.79/18.35  tff(c_1631, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1611, c_695])).
% 28.79/18.35  tff(c_1645, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1631])).
% 28.79/18.35  tff(c_2311, plain, (![D_332, A_333, B_334]: (v5_pre_topc(D_332, A_333, B_334) | ~v5_pre_topc(D_332, A_333, g1_pre_topc(u1_struct_0(B_334), u1_pre_topc(B_334))) | ~m1_subset_1(D_332, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_333), u1_struct_0(g1_pre_topc(u1_struct_0(B_334), u1_pre_topc(B_334)))))) | ~v1_funct_2(D_332, u1_struct_0(A_333), u1_struct_0(g1_pre_topc(u1_struct_0(B_334), u1_pre_topc(B_334)))) | ~m1_subset_1(D_332, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_333), u1_struct_0(B_334)))) | ~v1_funct_2(D_332, u1_struct_0(A_333), u1_struct_0(B_334)) | ~v1_funct_1(D_332) | ~l1_pre_topc(B_334) | ~v2_pre_topc(B_334) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.35  tff(c_2314, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_1621, c_2311])).
% 28.79/18.35  tff(c_2331, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1643, c_1645, c_94, c_92, c_84, c_1622, c_2314])).
% 28.79/18.35  tff(c_3793, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_2767, c_1619, c_2767, c_1613, c_2331])).
% 28.79/18.35  tff(c_2843, plain, (![D_394, A_395, B_396]: (v5_pre_topc(D_394, A_395, B_396) | ~v5_pre_topc(D_394, g1_pre_topc(u1_struct_0(A_395), u1_pre_topc(A_395)), B_396) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_395), u1_pre_topc(A_395))), u1_struct_0(B_396)))) | ~v1_funct_2(D_394, u1_struct_0(g1_pre_topc(u1_struct_0(A_395), u1_pre_topc(A_395))), u1_struct_0(B_396)) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_395), u1_struct_0(B_396)))) | ~v1_funct_2(D_394, u1_struct_0(A_395), u1_struct_0(B_396)) | ~v1_funct_1(D_394) | ~l1_pre_topc(B_396) | ~v2_pre_topc(B_396) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.35  tff(c_2852, plain, (![D_394, B_396]: (v5_pre_topc(D_394, '#skF_3', B_396) | ~v5_pre_topc(D_394, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_396) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(B_396)))) | ~v1_funct_2(D_394, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_396)) | ~m1_subset_1(D_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_396)))) | ~v1_funct_2(D_394, u1_struct_0('#skF_3'), u1_struct_0(B_396)) | ~v1_funct_1(D_394) | ~l1_pre_topc(B_396) | ~v2_pre_topc(B_396) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_2843])).
% 28.79/18.35  tff(c_17997, plain, (![D_4887, B_4888]: (v5_pre_topc(D_4887, '#skF_3', B_4888) | ~v5_pre_topc(D_4887, g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), B_4888) | ~m1_subset_1(D_4887, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_4888)))) | ~v1_funct_2(D_4887, k1_relat_1('#skF_6'), u1_struct_0(B_4888)) | ~v1_funct_1(D_4887) | ~l1_pre_topc(B_4888) | ~v2_pre_topc(B_4888))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_1611, c_1611, c_2767, c_1611, c_2767, c_1611, c_2852])).
% 28.79/18.35  tff(c_18006, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1619, c_17997])).
% 28.79/18.35  tff(c_18025, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_1620, c_3793, c_18006])).
% 28.79/18.35  tff(c_18027, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_18025])).
% 28.79/18.35  tff(c_18030, plain, (![A_4889]: (~r2_hidden(A_4889, '#skF_6'))), inference(splitRight, [status(thm)], [c_610])).
% 28.79/18.35  tff(c_18035, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_30, c_18030])).
% 28.79/18.35  tff(c_18063, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_2])).
% 28.79/18.35  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 28.79/18.35  tff(c_18060, plain, (![B_5]: (k2_zfmisc_1('#skF_6', B_5)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_18035, c_12])).
% 28.79/18.35  tff(c_18210, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_742])).
% 28.79/18.35  tff(c_18029, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_610])).
% 28.79/18.35  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 28.79/18.35  tff(c_18059, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_4])).
% 28.79/18.35  tff(c_18287, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_18029, c_18059])).
% 28.79/18.35  tff(c_8, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 28.79/18.35  tff(c_18531, plain, (![B_4925, A_4926]: (B_4925='#skF_6' | A_4926='#skF_6' | k2_zfmisc_1(A_4926, B_4925)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_18035, c_18035, c_8])).
% 28.79/18.35  tff(c_18545, plain, (u1_struct_0('#skF_4')='#skF_6' | u1_struct_0('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_18287, c_18531])).
% 28.79/18.35  tff(c_18550, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(splitLeft, [status(thm)], [c_18545])).
% 28.79/18.35  tff(c_18568, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_18550, c_82])).
% 28.79/18.35  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 28.79/18.35  tff(c_18061, plain, (![A_6]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_14])).
% 28.79/18.35  tff(c_18969, plain, (![C_4959, A_4960, B_4961]: (v1_partfun1(C_4959, A_4960) | ~v1_funct_2(C_4959, A_4960, B_4961) | ~v1_funct_1(C_4959) | ~m1_subset_1(C_4959, k1_zfmisc_1(k2_zfmisc_1(A_4960, B_4961))) | v1_xboole_0(B_4961))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.35  tff(c_18982, plain, (![A_4960, B_4961]: (v1_partfun1('#skF_6', A_4960) | ~v1_funct_2('#skF_6', A_4960, B_4961) | ~v1_funct_1('#skF_6') | v1_xboole_0(B_4961))), inference(resolution, [status(thm)], [c_18061, c_18969])).
% 28.79/18.35  tff(c_19738, plain, (![A_5025, B_5026]: (v1_partfun1('#skF_6', A_5025) | ~v1_funct_2('#skF_6', A_5025, B_5026) | v1_xboole_0(B_5026))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_18982])).
% 28.79/18.35  tff(c_19747, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_18568, c_19738])).
% 28.79/18.35  tff(c_19758, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_18210, c_19747])).
% 28.79/18.35  tff(c_154, plain, (![A_101]: (v1_xboole_0(k1_relat_1(A_101)) | ~v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_59])).
% 28.79/18.35  tff(c_165, plain, (![A_106]: (k1_relat_1(A_106)=k1_xboole_0 | ~v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_154, c_4])).
% 28.79/18.35  tff(c_173, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_165])).
% 28.79/18.35  tff(c_18056, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_18035, c_173])).
% 28.79/18.35  tff(c_542, plain, (![A_145]: (v4_relat_1(k1_xboole_0, A_145))), inference(resolution, [status(thm)], [c_14, c_512])).
% 28.79/18.35  tff(c_18044, plain, (![A_145]: (v4_relat_1('#skF_6', A_145))), inference(demodulation, [status(thm), theory('equality')], [c_18035, c_542])).
% 28.79/18.35  tff(c_18551, plain, (![B_4927, A_4928]: (k1_relat_1(B_4927)=A_4928 | ~v1_partfun1(B_4927, A_4928) | ~v4_relat_1(B_4927, A_4928) | ~v1_relat_1(B_4927))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.35  tff(c_18554, plain, (![A_145]: (k1_relat_1('#skF_6')=A_145 | ~v1_partfun1('#skF_6', A_145) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_18044, c_18551])).
% 28.79/18.35  tff(c_18560, plain, (![A_145]: (A_145='#skF_6' | ~v1_partfun1('#skF_6', A_145))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_18056, c_18554])).
% 28.79/18.35  tff(c_19766, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_19758, c_18560])).
% 28.79/18.35  tff(c_18565, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_18550, c_742])).
% 28.79/18.35  tff(c_19768, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_19766, c_18565])).
% 28.79/18.35  tff(c_19773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18063, c_18060, c_19768])).
% 28.79/18.35  tff(c_19774, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_18545])).
% 28.79/18.35  tff(c_19777, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_19774, c_18210])).
% 28.79/18.35  tff(c_19781, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_19774, c_82])).
% 28.79/18.35  tff(c_20218, plain, (![C_5062, A_5063, B_5064]: (v1_partfun1(C_5062, A_5063) | ~v1_funct_2(C_5062, A_5063, B_5064) | ~v1_funct_1(C_5062) | ~m1_subset_1(C_5062, k1_zfmisc_1(k2_zfmisc_1(A_5063, B_5064))) | v1_xboole_0(B_5064))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.35  tff(c_20231, plain, (![A_5063, B_5064]: (v1_partfun1('#skF_6', A_5063) | ~v1_funct_2('#skF_6', A_5063, B_5064) | ~v1_funct_1('#skF_6') | v1_xboole_0(B_5064))), inference(resolution, [status(thm)], [c_18061, c_20218])).
% 28.79/18.35  tff(c_21017, plain, (![A_5132, B_5133]: (v1_partfun1('#skF_6', A_5132) | ~v1_funct_2('#skF_6', A_5132, B_5133) | v1_xboole_0(B_5133))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_20231])).
% 28.79/18.35  tff(c_21026, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_19781, c_21017])).
% 28.79/18.35  tff(c_21037, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_19777, c_21026])).
% 28.79/18.35  tff(c_19895, plain, (![B_5034, A_5035]: (k1_relat_1(B_5034)=A_5035 | ~v1_partfun1(B_5034, A_5035) | ~v4_relat_1(B_5034, A_5035) | ~v1_relat_1(B_5034))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.35  tff(c_19898, plain, (![A_145]: (k1_relat_1('#skF_6')=A_145 | ~v1_partfun1('#skF_6', A_145) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_18044, c_19895])).
% 28.79/18.35  tff(c_19904, plain, (![A_145]: (A_145='#skF_6' | ~v1_partfun1('#skF_6', A_145))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_18056, c_19898])).
% 28.79/18.35  tff(c_21045, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_21037, c_19904])).
% 28.79/18.35  tff(c_19778, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_19774, c_742])).
% 28.79/18.35  tff(c_21047, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_21045, c_19778])).
% 28.79/18.35  tff(c_21052, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18063, c_18060, c_21047])).
% 28.79/18.35  tff(c_21054, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitRight, [status(thm)], [c_611])).
% 28.79/18.35  tff(c_21055, plain, (![A_5134]: (~r2_hidden(A_5134, '#skF_6'))), inference(splitRight, [status(thm)], [c_611])).
% 28.79/18.35  tff(c_21060, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_30, c_21055])).
% 28.79/18.35  tff(c_21084, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_4])).
% 28.79/18.35  tff(c_21395, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))='#skF_6'), inference(resolution, [status(thm)], [c_21054, c_21084])).
% 28.79/18.35  tff(c_21559, plain, (![B_5172, A_5173]: (B_5172='#skF_6' | A_5173='#skF_6' | k2_zfmisc_1(A_5173, B_5172)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_21060, c_8])).
% 28.79/18.35  tff(c_21572, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_21395, c_21559])).
% 28.79/18.35  tff(c_22040, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(splitLeft, [status(thm)], [c_21572])).
% 28.79/18.35  tff(c_22048, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_22040, c_695])).
% 28.79/18.35  tff(c_59465, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_22048])).
% 28.79/18.35  tff(c_59492, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_695, c_59465])).
% 28.79/18.35  tff(c_59496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_59492])).
% 28.79/18.35  tff(c_59498, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_22048])).
% 28.79/18.35  tff(c_371, plain, (![A_127, B_128]: (m1_subset_1('#skF_2'(A_127, B_128), k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 28.79/18.35  tff(c_383, plain, (![B_5]: (m1_subset_1('#skF_2'(k1_xboole_0, B_5), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_371])).
% 28.79/18.35  tff(c_593, plain, (![A_160, B_5]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_160, '#skF_2'(k1_xboole_0, B_5)))), inference(resolution, [status(thm)], [c_383, c_587])).
% 28.79/18.35  tff(c_624, plain, (![A_166, B_167]: (~r2_hidden(A_166, '#skF_2'(k1_xboole_0, B_167)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_593])).
% 28.79/18.35  tff(c_629, plain, (![B_167]: ('#skF_2'(k1_xboole_0, B_167)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_624])).
% 28.79/18.35  tff(c_21234, plain, (![B_5143]: ('#skF_2'('#skF_6', B_5143)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_629])).
% 28.79/18.35  tff(c_44, plain, (![A_41, B_42]: (v1_funct_2('#skF_2'(A_41, B_42), A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_124])).
% 28.79/18.35  tff(c_21242, plain, (![B_5143]: (v1_funct_2('#skF_6', '#skF_6', B_5143))), inference(superposition, [status(thm), theory('equality')], [c_21234, c_44])).
% 28.79/18.35  tff(c_21065, plain, (![B_167]: ('#skF_2'('#skF_6', B_167)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_629])).
% 28.79/18.35  tff(c_21086, plain, (![A_6]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_14])).
% 28.79/18.35  tff(c_58, plain, (![B_45, C_46, A_44]: (k1_xboole_0=B_45 | v1_partfun1(C_46, A_44) | ~v1_funct_2(C_46, A_44, B_45) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_1(C_46))), inference(cnfTransformation, [status(thm)], [f_141])).
% 28.79/18.35  tff(c_22102, plain, (![B_5227, C_5228, A_5229]: (B_5227='#skF_6' | v1_partfun1(C_5228, A_5229) | ~v1_funct_2(C_5228, A_5229, B_5227) | ~m1_subset_1(C_5228, k1_zfmisc_1(k2_zfmisc_1(A_5229, B_5227))) | ~v1_funct_1(C_5228))), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_58])).
% 28.79/18.35  tff(c_22118, plain, (![B_5227, A_5229]: (B_5227='#skF_6' | v1_partfun1('#skF_6', A_5229) | ~v1_funct_2('#skF_6', A_5229, B_5227) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_21086, c_22102])).
% 28.79/18.35  tff(c_22256, plain, (![B_5238, A_5239]: (B_5238='#skF_6' | v1_partfun1('#skF_6', A_5239) | ~v1_funct_2('#skF_6', A_5239, B_5238))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_22118])).
% 28.79/18.35  tff(c_22278, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_22256])).
% 28.79/18.35  tff(c_22279, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_22278])).
% 28.79/18.35  tff(c_21081, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_173])).
% 28.79/18.35  tff(c_21069, plain, (![A_145]: (v4_relat_1('#skF_6', A_145))), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_542])).
% 28.79/18.35  tff(c_21647, plain, (![B_5177, A_5178]: (k1_relat_1(B_5177)=A_5178 | ~v1_partfun1(B_5177, A_5178) | ~v4_relat_1(B_5177, A_5178) | ~v1_relat_1(B_5177))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.35  tff(c_21650, plain, (![A_145]: (k1_relat_1('#skF_6')=A_145 | ~v1_partfun1('#skF_6', A_145) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_21069, c_21647])).
% 28.79/18.35  tff(c_21656, plain, (![A_145]: (A_145='#skF_6' | ~v1_partfun1('#skF_6', A_145))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_21081, c_21650])).
% 28.79/18.35  tff(c_22283, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_22279, c_21656])).
% 28.79/18.35  tff(c_22286, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_22283, c_387])).
% 28.79/18.35  tff(c_22285, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22283, c_22040])).
% 28.79/18.35  tff(c_21085, plain, (![B_5]: (k2_zfmisc_1('#skF_6', B_5)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_12])).
% 28.79/18.35  tff(c_46, plain, (![A_41, B_42]: (v1_funct_1('#skF_2'(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 28.79/18.35  tff(c_54, plain, (![A_41, B_42]: (m1_subset_1('#skF_2'(A_41, B_42), k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 28.79/18.35  tff(c_28638, plain, (![D_5571, A_5572, B_5573]: (v5_pre_topc(D_5571, A_5572, B_5573) | ~v5_pre_topc(D_5571, g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572)), B_5573) | ~m1_subset_1(D_5571, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)))) | ~v1_funct_2(D_5571, u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)) | ~m1_subset_1(D_5571, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5572), u1_struct_0(B_5573)))) | ~v1_funct_2(D_5571, u1_struct_0(A_5572), u1_struct_0(B_5573)) | ~v1_funct_1(D_5571) | ~l1_pre_topc(B_5573) | ~v2_pre_topc(B_5573) | ~l1_pre_topc(A_5572) | ~v2_pre_topc(A_5572))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.35  tff(c_28658, plain, (![A_5572, B_5573]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)), A_5572, B_5573) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)), g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572)), B_5573) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)), u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5572), u1_struct_0(B_5573)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573)), u1_struct_0(A_5572), u1_struct_0(B_5573)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5572), u1_pre_topc(A_5572))), u1_struct_0(B_5573))) | ~l1_pre_topc(B_5573) | ~v2_pre_topc(B_5573) | ~l1_pre_topc(A_5572) | ~v2_pre_topc(A_5572))), inference(resolution, [status(thm)], [c_54, c_28638])).
% 28.79/18.35  tff(c_29017, plain, (![A_5613, B_5614]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613), u1_pre_topc(A_5613))), u1_struct_0(B_5614)), A_5613, B_5614) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613), u1_pre_topc(A_5613))), u1_struct_0(B_5614)), g1_pre_topc(u1_struct_0(A_5613), u1_pre_topc(A_5613)), B_5614) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613), u1_pre_topc(A_5613))), u1_struct_0(B_5614)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5613), u1_struct_0(B_5614)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5613), u1_pre_topc(A_5613))), u1_struct_0(B_5614)), u1_struct_0(A_5613), u1_struct_0(B_5614)) | ~l1_pre_topc(B_5614) | ~v2_pre_topc(B_5614) | ~l1_pre_topc(A_5613) | ~v2_pre_topc(A_5613))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_28658])).
% 28.79/18.35  tff(c_29025, plain, (![B_5614]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_5614)), '#skF_3', B_5614) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(B_5614)), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_5614) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_5614)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_5614)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_5614)), u1_struct_0('#skF_3'), u1_struct_0(B_5614)) | ~l1_pre_topc(B_5614) | ~v2_pre_topc(B_5614) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22283, c_29017])).
% 28.79/18.35  tff(c_29044, plain, (![B_5615]: (v5_pre_topc('#skF_6', '#skF_3', B_5615) | ~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_5615) | ~l1_pre_topc(B_5615) | ~v2_pre_topc(B_5615))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_21242, c_21065, c_22283, c_22285, c_22283, c_21086, c_21085, c_21065, c_22283, c_22285, c_22283, c_21065, c_22283, c_22285, c_21065, c_22285, c_22283, c_29025])).
% 28.79/18.35  tff(c_29048, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_22286, c_29044])).
% 28.79/18.35  tff(c_29281, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_29048])).
% 28.79/18.35  tff(c_29284, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_29281])).
% 28.79/18.35  tff(c_29288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_29284])).
% 28.79/18.35  tff(c_29289, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_29048])).
% 28.79/18.35  tff(c_29372, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_29289])).
% 28.79/18.35  tff(c_29375, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_695, c_29372])).
% 28.79/18.35  tff(c_29379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_29375])).
% 28.79/18.35  tff(c_29380, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_29289])).
% 28.79/18.35  tff(c_22561, plain, (![D_5255, A_5256, B_5257]: (v5_pre_topc(D_5255, A_5256, B_5257) | ~v5_pre_topc(D_5255, A_5256, g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257))) | ~m1_subset_1(D_5255, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))))) | ~v1_funct_2(D_5255, u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))) | ~m1_subset_1(D_5255, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5256), u1_struct_0(B_5257)))) | ~v1_funct_2(D_5255, u1_struct_0(A_5256), u1_struct_0(B_5257)) | ~v1_funct_1(D_5255) | ~l1_pre_topc(B_5257) | ~v2_pre_topc(B_5257) | ~l1_pre_topc(A_5256) | ~v2_pre_topc(A_5256))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.35  tff(c_22581, plain, (![A_5256, B_5257]: (v5_pre_topc('#skF_2'(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))), A_5256, B_5257) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))), A_5256, g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))), u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5256), u1_struct_0(B_5257)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257)))), u1_struct_0(A_5256), u1_struct_0(B_5257)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_5256), u1_struct_0(g1_pre_topc(u1_struct_0(B_5257), u1_pre_topc(B_5257))))) | ~l1_pre_topc(B_5257) | ~v2_pre_topc(B_5257) | ~l1_pre_topc(A_5256) | ~v2_pre_topc(A_5256))), inference(resolution, [status(thm)], [c_54, c_22561])).
% 28.79/18.35  tff(c_29304, plain, (![A_5648, B_5649]: (v5_pre_topc('#skF_2'(u1_struct_0(A_5648), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), A_5648, B_5649) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_5648), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), A_5648, g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_5648), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5648), u1_struct_0(B_5649)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_5648), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), u1_struct_0(A_5648), u1_struct_0(B_5649)) | ~l1_pre_topc(B_5649) | ~v2_pre_topc(B_5649) | ~l1_pre_topc(A_5648) | ~v2_pre_topc(A_5648))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_22581])).
% 28.79/18.35  tff(c_29312, plain, (![B_5649]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), '#skF_3', B_5649) | ~v5_pre_topc('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), '#skF_3', g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649))) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_5649)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_5649), u1_pre_topc(B_5649)))), u1_struct_0('#skF_3'), u1_struct_0(B_5649)) | ~l1_pre_topc(B_5649) | ~v2_pre_topc(B_5649) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22283, c_29304])).
% 28.79/18.35  tff(c_32264, plain, (![B_5793]: (v5_pre_topc('#skF_6', '#skF_3', B_5793) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_5793), u1_pre_topc(B_5793))) | ~l1_pre_topc(B_5793) | ~v2_pre_topc(B_5793))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_21242, c_21065, c_22283, c_22283, c_21086, c_21085, c_21065, c_22283, c_22283, c_21065, c_21065, c_22283, c_29312])).
% 28.79/18.35  tff(c_32273, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_29380, c_32264])).
% 28.79/18.35  tff(c_32285, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_32273])).
% 28.79/18.35  tff(c_32287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_32285])).
% 28.79/18.35  tff(c_32288, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_22278])).
% 28.79/18.35  tff(c_32290, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_32288, c_387])).
% 28.79/18.35  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 28.79/18.35  tff(c_21083, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_10])).
% 28.79/18.35  tff(c_48741, plain, (![D_8929, A_8930, B_8931]: (v5_pre_topc(D_8929, A_8930, B_8931) | ~v5_pre_topc(D_8929, A_8930, g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931))) | ~m1_subset_1(D_8929, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))))) | ~v1_funct_2(D_8929, u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))) | ~m1_subset_1(D_8929, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8930), u1_struct_0(B_8931)))) | ~v1_funct_2(D_8929, u1_struct_0(A_8930), u1_struct_0(B_8931)) | ~v1_funct_1(D_8929) | ~l1_pre_topc(B_8931) | ~v2_pre_topc(B_8931) | ~l1_pre_topc(A_8930) | ~v2_pre_topc(A_8930))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.35  tff(c_48764, plain, (![A_8930, B_8931]: (v5_pre_topc('#skF_2'(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))), A_8930, B_8931) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))), A_8930, g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))), u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8930), u1_struct_0(B_8931)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931)))), u1_struct_0(A_8930), u1_struct_0(B_8931)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_8930), u1_struct_0(g1_pre_topc(u1_struct_0(B_8931), u1_pre_topc(B_8931))))) | ~l1_pre_topc(B_8931) | ~v2_pre_topc(B_8931) | ~l1_pre_topc(A_8930) | ~v2_pre_topc(A_8930))), inference(resolution, [status(thm)], [c_54, c_48741])).
% 28.79/18.35  tff(c_49096, plain, (![A_8973, B_8974]: (v5_pre_topc('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0(B_8974), u1_pre_topc(B_8974)))), A_8973, B_8974) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0(B_8974), u1_pre_topc(B_8974)))), A_8973, g1_pre_topc(u1_struct_0(B_8974), u1_pre_topc(B_8974))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0(B_8974), u1_pre_topc(B_8974)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8973), u1_struct_0(B_8974)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0(B_8974), u1_pre_topc(B_8974)))), u1_struct_0(A_8973), u1_struct_0(B_8974)) | ~l1_pre_topc(B_8974) | ~v2_pre_topc(B_8974) | ~l1_pre_topc(A_8973) | ~v2_pre_topc(A_8973))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_48764])).
% 28.79/18.35  tff(c_49100, plain, (![A_8973]: (v5_pre_topc('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_8973, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), A_8973, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_8973), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_8973), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_8973), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_8973) | ~v2_pre_topc(A_8973))), inference(superposition, [status(thm), theory('equality')], [c_32288, c_49096])).
% 28.79/18.35  tff(c_61526, plain, (![A_12695]: (v5_pre_topc('#skF_2'(u1_struct_0(A_12695), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), A_12695, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(A_12695), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), A_12695, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_12695), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_2'(u1_struct_0(A_12695), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), u1_struct_0(A_12695), '#skF_6') | ~l1_pre_topc(A_12695) | ~v2_pre_topc(A_12695))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_32288, c_32288, c_21083, c_32288, c_32288, c_32288, c_32288, c_49100])).
% 28.79/18.35  tff(c_61532, plain, (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v5_pre_topc('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_22040, c_61526])).
% 28.79/18.35  tff(c_61537, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_59498, c_21242, c_21065, c_22040, c_22040, c_21086, c_21065, c_22040, c_32290, c_21065, c_21065, c_22040, c_61532])).
% 28.79/18.35  tff(c_61564, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_61537])).
% 28.79/18.35  tff(c_61567, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_61564])).
% 28.79/18.35  tff(c_61571, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_61567])).
% 28.79/18.35  tff(c_61572, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_61537])).
% 28.79/18.35  tff(c_380, plain, (![A_4]: (m1_subset_1('#skF_2'(A_4, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_371])).
% 28.79/18.35  tff(c_591, plain, (![A_160, A_4]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_160, '#skF_2'(A_4, k1_xboole_0)))), inference(resolution, [status(thm)], [c_380, c_587])).
% 28.79/18.35  tff(c_678, plain, (![A_170, A_171]: (~r2_hidden(A_170, '#skF_2'(A_171, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_591])).
% 28.79/18.35  tff(c_705, plain, (![A_175]: ('#skF_2'(A_175, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_678])).
% 28.79/18.35  tff(c_716, plain, (![A_175]: (v1_funct_2(k1_xboole_0, A_175, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_705, c_44])).
% 28.79/18.35  tff(c_21061, plain, (![A_175]: (v1_funct_2('#skF_6', A_175, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_716])).
% 28.79/18.35  tff(c_686, plain, (![A_171]: ('#skF_2'(A_171, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_678])).
% 28.79/18.35  tff(c_21062, plain, (![A_171]: ('#skF_2'(A_171, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_21060, c_686])).
% 28.79/18.35  tff(c_32494, plain, (![D_5805, A_5806, B_5807]: (v5_pre_topc(D_5805, A_5806, B_5807) | ~v5_pre_topc(D_5805, g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806)), B_5807) | ~m1_subset_1(D_5805, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)))) | ~v1_funct_2(D_5805, u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)) | ~m1_subset_1(D_5805, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5806), u1_struct_0(B_5807)))) | ~v1_funct_2(D_5805, u1_struct_0(A_5806), u1_struct_0(B_5807)) | ~v1_funct_1(D_5805) | ~l1_pre_topc(B_5807) | ~v2_pre_topc(B_5807) | ~l1_pre_topc(A_5806) | ~v2_pre_topc(A_5806))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.35  tff(c_32517, plain, (![A_5806, B_5807]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)), A_5806, B_5807) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)), g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806)), B_5807) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)), u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5806), u1_struct_0(B_5807)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807)), u1_struct_0(A_5806), u1_struct_0(B_5807)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5806), u1_pre_topc(A_5806))), u1_struct_0(B_5807))) | ~l1_pre_topc(B_5807) | ~v2_pre_topc(B_5807) | ~l1_pre_topc(A_5806) | ~v2_pre_topc(A_5806))), inference(resolution, [status(thm)], [c_54, c_32494])).
% 28.79/18.35  tff(c_49415, plain, (![A_9009, B_9010]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0(B_9010)), A_9009, B_9010) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0(B_9010)), g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009)), B_9010) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0(B_9010)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9009), u1_struct_0(B_9010)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0(B_9010)), u1_struct_0(A_9009), u1_struct_0(B_9010)) | ~l1_pre_topc(B_9010) | ~v2_pre_topc(B_9010) | ~l1_pre_topc(A_9009) | ~v2_pre_topc(A_9009))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_32517])).
% 28.79/18.35  tff(c_49419, plain, (![A_9009]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0('#skF_4')), A_9009, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), '#skF_6'), g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009)), '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_9009), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009))), u1_struct_0('#skF_4')), u1_struct_0(A_9009), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_9009) | ~v2_pre_topc(A_9009))), inference(superposition, [status(thm), theory('equality')], [c_32288, c_49415])).
% 28.79/18.35  tff(c_49433, plain, (![A_9009]: (v5_pre_topc('#skF_6', A_9009, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_9009), u1_pre_topc(A_9009)), '#skF_4') | ~l1_pre_topc(A_9009) | ~v2_pre_topc(A_9009))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_21061, c_21062, c_32288, c_32288, c_21086, c_21083, c_21062, c_32288, c_32288, c_21062, c_21062, c_32288, c_49419])).
% 28.79/18.35  tff(c_61576, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_61572, c_49433])).
% 28.79/18.35  tff(c_61579, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_61576])).
% 28.79/18.35  tff(c_61581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_61579])).
% 28.79/18.35  tff(c_61582, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_21572])).
% 28.79/18.35  tff(c_61637, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61582, c_695])).
% 28.79/18.35  tff(c_66202, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_61637])).
% 28.79/18.35  tff(c_66205, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_695, c_66202])).
% 28.79/18.35  tff(c_66209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_66205])).
% 28.79/18.35  tff(c_66211, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_61637])).
% 28.79/18.35  tff(c_61640, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61582, c_66])).
% 28.79/18.35  tff(c_69010, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66211, c_61640])).
% 28.79/18.35  tff(c_69011, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_69010])).
% 28.79/18.35  tff(c_69014, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_69011])).
% 28.79/18.35  tff(c_69018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_69014])).
% 28.79/18.35  tff(c_69020, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_69010])).
% 28.79/18.35  tff(c_61585, plain, (![B_12699, C_12700, A_12701]: (B_12699='#skF_6' | v1_partfun1(C_12700, A_12701) | ~v1_funct_2(C_12700, A_12701, B_12699) | ~m1_subset_1(C_12700, k1_zfmisc_1(k2_zfmisc_1(A_12701, B_12699))) | ~v1_funct_1(C_12700))), inference(demodulation, [status(thm), theory('equality')], [c_21060, c_58])).
% 28.79/18.35  tff(c_61604, plain, (![B_12699, A_12701]: (B_12699='#skF_6' | v1_partfun1('#skF_6', A_12701) | ~v1_funct_2('#skF_6', A_12701, B_12699) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_21086, c_61585])).
% 28.79/18.35  tff(c_61652, plain, (![B_12707, A_12708]: (B_12707='#skF_6' | v1_partfun1('#skF_6', A_12708) | ~v1_funct_2('#skF_6', A_12708, B_12707))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_61604])).
% 28.79/18.35  tff(c_61674, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_61652])).
% 28.79/18.35  tff(c_61675, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_61674])).
% 28.79/18.35  tff(c_61679, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_61675, c_21656])).
% 28.79/18.35  tff(c_61682, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_61679, c_387])).
% 28.79/18.35  tff(c_61769, plain, (![D_12714, A_12715, B_12716]: (v5_pre_topc(D_12714, A_12715, B_12716) | ~v5_pre_topc(D_12714, g1_pre_topc(u1_struct_0(A_12715), u1_pre_topc(A_12715)), B_12716) | ~m1_subset_1(D_12714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_12715), u1_pre_topc(A_12715))), u1_struct_0(B_12716)))) | ~v1_funct_2(D_12714, u1_struct_0(g1_pre_topc(u1_struct_0(A_12715), u1_pre_topc(A_12715))), u1_struct_0(B_12716)) | ~m1_subset_1(D_12714, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12715), u1_struct_0(B_12716)))) | ~v1_funct_2(D_12714, u1_struct_0(A_12715), u1_struct_0(B_12716)) | ~v1_funct_1(D_12714) | ~l1_pre_topc(B_12716) | ~v2_pre_topc(B_12716) | ~l1_pre_topc(A_12715) | ~v2_pre_topc(A_12715))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.35  tff(c_61788, plain, (![A_12715, B_12716]: (v5_pre_topc('#skF_6', A_12715, B_12716) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_12715), u1_pre_topc(A_12715)), B_12716) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_12715), u1_pre_topc(A_12715))), u1_struct_0(B_12716)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12715), u1_struct_0(B_12716)))) | ~v1_funct_2('#skF_6', u1_struct_0(A_12715), u1_struct_0(B_12716)) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(B_12716) | ~v2_pre_topc(B_12716) | ~l1_pre_topc(A_12715) | ~v2_pre_topc(A_12715))), inference(resolution, [status(thm)], [c_21086, c_61769])).
% 28.79/18.35  tff(c_69402, plain, (![A_13199, B_13200]: (v5_pre_topc('#skF_6', A_13199, B_13200) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_13199), u1_pre_topc(A_13199)), B_13200) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_13199), u1_pre_topc(A_13199))), u1_struct_0(B_13200)) | ~v1_funct_2('#skF_6', u1_struct_0(A_13199), u1_struct_0(B_13200)) | ~l1_pre_topc(B_13200) | ~v2_pre_topc(B_13200) | ~l1_pre_topc(A_13199) | ~v2_pre_topc(A_13199))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21086, c_61788])).
% 28.79/18.35  tff(c_69408, plain, (![B_13200]: (v5_pre_topc('#skF_6', '#skF_3', B_13200) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_13200) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(B_13200)) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0(B_13200)) | ~l1_pre_topc(B_13200) | ~v2_pre_topc(B_13200) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61679, c_69402])).
% 28.79/18.35  tff(c_69798, plain, (![B_13219]: (v5_pre_topc('#skF_6', '#skF_3', B_13219) | ~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_13219) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(B_13219)) | ~l1_pre_topc(B_13219) | ~v2_pre_topc(B_13219))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_21242, c_61679, c_61679, c_69408])).
% 28.79/18.35  tff(c_69807, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_61582, c_69798])).
% 28.79/18.35  tff(c_69813, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_69020, c_66211, c_21061, c_61682, c_69807])).
% 28.79/18.35  tff(c_66099, plain, (![D_12987, A_12988, B_12989]: (v5_pre_topc(D_12987, A_12988, B_12989) | ~v5_pre_topc(D_12987, A_12988, g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989))) | ~m1_subset_1(D_12987, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))))) | ~v1_funct_2(D_12987, u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))) | ~m1_subset_1(D_12987, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988), u1_struct_0(B_12989)))) | ~v1_funct_2(D_12987, u1_struct_0(A_12988), u1_struct_0(B_12989)) | ~v1_funct_1(D_12987) | ~l1_pre_topc(B_12989) | ~v2_pre_topc(B_12989) | ~l1_pre_topc(A_12988) | ~v2_pre_topc(A_12988))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.35  tff(c_66122, plain, (![A_12988, B_12989]: (v5_pre_topc('#skF_2'(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))), A_12988, B_12989) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))), A_12988, g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))), u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_12988), u1_struct_0(B_12989)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989)))), u1_struct_0(A_12988), u1_struct_0(B_12989)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_12988), u1_struct_0(g1_pre_topc(u1_struct_0(B_12989), u1_pre_topc(B_12989))))) | ~l1_pre_topc(B_12989) | ~v2_pre_topc(B_12989) | ~l1_pre_topc(A_12988) | ~v2_pre_topc(A_12988))), inference(resolution, [status(thm)], [c_54, c_66099])).
% 28.79/18.35  tff(c_66652, plain, (![A_13041, B_13042]: (v5_pre_topc('#skF_2'(u1_struct_0(A_13041), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), A_13041, B_13042) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_13041), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), A_13041, g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_13041), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13041), u1_struct_0(B_13042)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_13041), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), u1_struct_0(A_13041), u1_struct_0(B_13042)) | ~l1_pre_topc(B_13042) | ~v2_pre_topc(B_13042) | ~l1_pre_topc(A_13041) | ~v2_pre_topc(A_13041))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_66122])).
% 28.79/18.35  tff(c_66654, plain, (![B_13042]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), '#skF_3', B_13042) | ~v5_pre_topc('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), '#skF_3', g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042))) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_13042)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042)))), u1_struct_0('#skF_3'), u1_struct_0(B_13042)) | ~l1_pre_topc(B_13042) | ~v2_pre_topc(B_13042) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61679, c_66652])).
% 28.79/18.35  tff(c_66668, plain, (![B_13042]: (v5_pre_topc('#skF_6', '#skF_3', B_13042) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_13042), u1_pre_topc(B_13042))) | ~l1_pre_topc(B_13042) | ~v2_pre_topc(B_13042))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_21242, c_21065, c_61679, c_61679, c_21086, c_21085, c_21065, c_61679, c_61679, c_21065, c_21065, c_61679, c_66654])).
% 28.79/18.35  tff(c_69816, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_69813, c_66668])).
% 28.79/18.35  tff(c_69819, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_69816])).
% 28.79/18.35  tff(c_69821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_69819])).
% 28.79/18.35  tff(c_69822, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_61674])).
% 28.79/18.35  tff(c_69825, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_69822, c_387])).
% 28.79/18.35  tff(c_69824, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_69822, c_61582])).
% 28.79/18.35  tff(c_77670, plain, (![D_13610, A_13611, B_13612]: (v5_pre_topc(D_13610, A_13611, B_13612) | ~v5_pre_topc(D_13610, A_13611, g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612))) | ~m1_subset_1(D_13610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))))) | ~v1_funct_2(D_13610, u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))) | ~m1_subset_1(D_13610, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13611), u1_struct_0(B_13612)))) | ~v1_funct_2(D_13610, u1_struct_0(A_13611), u1_struct_0(B_13612)) | ~v1_funct_1(D_13610) | ~l1_pre_topc(B_13612) | ~v2_pre_topc(B_13612) | ~l1_pre_topc(A_13611) | ~v2_pre_topc(A_13611))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.35  tff(c_77690, plain, (![A_13611, B_13612]: (v5_pre_topc('#skF_2'(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))), A_13611, B_13612) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))), A_13611, g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))), u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13611), u1_struct_0(B_13612)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612)))), u1_struct_0(A_13611), u1_struct_0(B_13612)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_13611), u1_struct_0(g1_pre_topc(u1_struct_0(B_13612), u1_pre_topc(B_13612))))) | ~l1_pre_topc(B_13612) | ~v2_pre_topc(B_13612) | ~l1_pre_topc(A_13611) | ~v2_pre_topc(A_13611))), inference(resolution, [status(thm)], [c_54, c_77670])).
% 28.79/18.35  tff(c_78400, plain, (![A_13677, B_13678]: (v5_pre_topc('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0(B_13678), u1_pre_topc(B_13678)))), A_13677, B_13678) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0(B_13678), u1_pre_topc(B_13678)))), A_13677, g1_pre_topc(u1_struct_0(B_13678), u1_pre_topc(B_13678))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0(B_13678), u1_pre_topc(B_13678)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13677), u1_struct_0(B_13678)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0(B_13678), u1_pre_topc(B_13678)))), u1_struct_0(A_13677), u1_struct_0(B_13678)) | ~l1_pre_topc(B_13678) | ~v2_pre_topc(B_13678) | ~l1_pre_topc(A_13677) | ~v2_pre_topc(A_13677))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_77690])).
% 28.79/18.35  tff(c_78415, plain, (![A_13677]: (v5_pre_topc('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_13677, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_13677, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13677), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_13677), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_13677), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_13677) | ~v2_pre_topc(A_13677))), inference(superposition, [status(thm), theory('equality')], [c_69822, c_78400])).
% 28.79/18.35  tff(c_78466, plain, (![A_13685]: (v5_pre_topc('#skF_6', A_13685, '#skF_4') | ~v5_pre_topc('#skF_6', A_13685, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_13685) | ~v2_pre_topc(A_13685))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_21061, c_21062, c_69822, c_69824, c_69822, c_21086, c_21083, c_21062, c_69822, c_69824, c_69822, c_21062, c_69824, c_69822, c_21062, c_69824, c_69822, c_78415])).
% 28.79/18.35  tff(c_78484, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_69825, c_78466])).
% 28.79/18.35  tff(c_78711, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_78484])).
% 28.79/18.35  tff(c_78714, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_78711])).
% 28.79/18.35  tff(c_78718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_78714])).
% 28.79/18.35  tff(c_78719, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_78484])).
% 28.79/18.35  tff(c_78842, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_78719])).
% 28.79/18.35  tff(c_78845, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_695, c_78842])).
% 28.79/18.35  tff(c_78849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_78845])).
% 28.79/18.35  tff(c_78850, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_78719])).
% 28.79/18.35  tff(c_69935, plain, (![D_13225, A_13226, B_13227]: (v5_pre_topc(D_13225, A_13226, B_13227) | ~v5_pre_topc(D_13225, g1_pre_topc(u1_struct_0(A_13226), u1_pre_topc(A_13226)), B_13227) | ~m1_subset_1(D_13225, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_13226), u1_pre_topc(A_13226))), u1_struct_0(B_13227)))) | ~v1_funct_2(D_13225, u1_struct_0(g1_pre_topc(u1_struct_0(A_13226), u1_pre_topc(A_13226))), u1_struct_0(B_13227)) | ~m1_subset_1(D_13225, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13226), u1_struct_0(B_13227)))) | ~v1_funct_2(D_13225, u1_struct_0(A_13226), u1_struct_0(B_13227)) | ~v1_funct_1(D_13225) | ~l1_pre_topc(B_13227) | ~v2_pre_topc(B_13227) | ~l1_pre_topc(A_13226) | ~v2_pre_topc(A_13226))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.35  tff(c_69951, plain, (![A_13226, B_13227]: (v5_pre_topc('#skF_6', A_13226, B_13227) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_13226), u1_pre_topc(A_13226)), B_13227) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_13226), u1_pre_topc(A_13226))), u1_struct_0(B_13227)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13226), u1_struct_0(B_13227)))) | ~v1_funct_2('#skF_6', u1_struct_0(A_13226), u1_struct_0(B_13227)) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(B_13227) | ~v2_pre_topc(B_13227) | ~l1_pre_topc(A_13226) | ~v2_pre_topc(A_13226))), inference(resolution, [status(thm)], [c_21086, c_69935])).
% 28.79/18.35  tff(c_81367, plain, (![A_13855, B_13856]: (v5_pre_topc('#skF_6', A_13855, B_13856) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_13855), u1_pre_topc(A_13855)), B_13856) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_13855), u1_pre_topc(A_13855))), u1_struct_0(B_13856)) | ~v1_funct_2('#skF_6', u1_struct_0(A_13855), u1_struct_0(B_13856)) | ~l1_pre_topc(B_13856) | ~v2_pre_topc(B_13856) | ~l1_pre_topc(A_13855) | ~v2_pre_topc(A_13855))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_21086, c_69951])).
% 28.79/18.35  tff(c_81382, plain, (![A_13855]: (v5_pre_topc('#skF_6', A_13855, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_13855), u1_pre_topc(A_13855)), '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_13855), u1_pre_topc(A_13855))), '#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0(A_13855), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_13855) | ~v2_pre_topc(A_13855))), inference(superposition, [status(thm), theory('equality')], [c_69822, c_81367])).
% 28.79/18.35  tff(c_82427, plain, (![A_13913]: (v5_pre_topc('#skF_6', A_13913, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_13913), u1_pre_topc(A_13913)), '#skF_4') | ~l1_pre_topc(A_13913) | ~v2_pre_topc(A_13913))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_21061, c_69822, c_21061, c_81382])).
% 28.79/18.35  tff(c_82436, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78850, c_82427])).
% 28.79/18.35  tff(c_82449, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_82436])).
% 28.79/18.35  tff(c_82451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_82449])).
% 28.79/18.35  tff(c_82452, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_110])).
% 28.79/18.35  tff(c_82926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_387, c_82452])).
% 28.79/18.35  tff(c_82927, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_108])).
% 28.79/18.35  tff(c_83184, plain, (![A_13999]: (m1_subset_1(u1_pre_topc(A_13999), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13999)))) | ~l1_pre_topc(A_13999))), inference(cnfTransformation, [status(thm)], [f_151])).
% 28.79/18.36  tff(c_60, plain, (![A_47, B_48]: (l1_pre_topc(g1_pre_topc(A_47, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 28.79/18.36  tff(c_83193, plain, (![A_13999]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_13999), u1_pre_topc(A_13999))) | ~l1_pre_topc(A_13999))), inference(resolution, [status(thm)], [c_83184, c_60])).
% 28.79/18.36  tff(c_83016, plain, (![C_13977, B_13978, A_13979]: (~v1_xboole_0(C_13977) | ~m1_subset_1(B_13978, k1_zfmisc_1(C_13977)) | ~r2_hidden(A_13979, B_13978))), inference(cnfTransformation, [status(thm)], [f_55])).
% 28.79/18.36  tff(c_83036, plain, (![A_13979]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))) | ~r2_hidden(A_13979, '#skF_6'))), inference(resolution, [status(thm)], [c_111, c_83016])).
% 28.79/18.36  tff(c_83243, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_83036])).
% 28.79/18.36  tff(c_83247, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_83243])).
% 28.79/18.36  tff(c_83086, plain, (![C_13984, A_13985, B_13986]: (v4_relat_1(C_13984, A_13985) | ~m1_subset_1(C_13984, k1_zfmisc_1(k2_zfmisc_1(A_13985, B_13986))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 28.79/18.36  tff(c_83114, plain, (v4_relat_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_111, c_83086])).
% 28.79/18.36  tff(c_83768, plain, (![B_14077, A_14078]: (k1_relat_1(B_14077)=A_14078 | ~v1_partfun1(B_14077, A_14078) | ~v4_relat_1(B_14077, A_14078) | ~v1_relat_1(B_14077))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.36  tff(c_83777, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_83114, c_83768])).
% 28.79/18.36  tff(c_83795, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_83777])).
% 28.79/18.36  tff(c_84185, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_83795])).
% 28.79/18.36  tff(c_84385, plain, (![C_14109, A_14110, B_14111]: (v1_partfun1(C_14109, A_14110) | ~v1_funct_2(C_14109, A_14110, B_14111) | ~v1_funct_1(C_14109) | ~m1_subset_1(C_14109, k1_zfmisc_1(k2_zfmisc_1(A_14110, B_14111))) | v1_xboole_0(B_14111))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.36  tff(c_84397, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_111, c_84385])).
% 28.79/18.36  tff(c_84413, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_84397])).
% 28.79/18.36  tff(c_84415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83247, c_84185, c_84413])).
% 28.79/18.36  tff(c_84416, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_83795])).
% 28.79/18.36  tff(c_83015, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82927, c_110])).
% 28.79/18.36  tff(c_84424, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_84416, c_83015])).
% 28.79/18.36  tff(c_83037, plain, (![A_13979]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~r2_hidden(A_13979, '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_83016])).
% 28.79/18.36  tff(c_83183, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitLeft, [status(thm)], [c_83037])).
% 28.79/18.36  tff(c_83506, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_83183])).
% 28.79/18.36  tff(c_83812, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_83795])).
% 28.79/18.36  tff(c_83939, plain, (![C_14088, A_14089, B_14090]: (v1_partfun1(C_14088, A_14089) | ~v1_funct_2(C_14088, A_14089, B_14090) | ~v1_funct_1(C_14088) | ~m1_subset_1(C_14088, k1_zfmisc_1(k2_zfmisc_1(A_14089, B_14090))) | v1_xboole_0(B_14090))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.36  tff(c_83951, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_111, c_83939])).
% 28.79/18.36  tff(c_83970, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_107, c_83951])).
% 28.79/18.36  tff(c_83972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83247, c_83812, c_83970])).
% 28.79/18.36  tff(c_83973, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_83795])).
% 28.79/18.36  tff(c_83115, plain, (v4_relat_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_80, c_83086])).
% 28.79/18.36  tff(c_83780, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_83115, c_83768])).
% 28.79/18.36  tff(c_83798, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_83780])).
% 28.79/18.36  tff(c_83805, plain, (~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_83798])).
% 28.79/18.36  tff(c_84084, plain, (~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_83973, c_83805])).
% 28.79/18.36  tff(c_83985, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_83973, c_82])).
% 28.79/18.36  tff(c_83984, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_83973, c_80])).
% 28.79/18.36  tff(c_36, plain, (![C_38, A_35, B_36]: (v1_partfun1(C_38, A_35) | ~v1_funct_2(C_38, A_35, B_36) | ~v1_funct_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))) | v1_xboole_0(B_36))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.36  tff(c_84158, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_83984, c_36])).
% 28.79/18.36  tff(c_84174, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_83985, c_84158])).
% 28.79/18.36  tff(c_84176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83506, c_84084, c_84174])).
% 28.79/18.36  tff(c_84177, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_83798])).
% 28.79/18.36  tff(c_84570, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84416, c_84177])).
% 28.79/18.36  tff(c_84428, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_84416, c_82])).
% 28.79/18.36  tff(c_84574, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_84570, c_84428])).
% 28.79/18.36  tff(c_84427, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_84416, c_80])).
% 28.79/18.36  tff(c_84572, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_84570, c_84427])).
% 28.79/18.36  tff(c_85219, plain, (![D_14161, A_14162, B_14163]: (v5_pre_topc(D_14161, g1_pre_topc(u1_struct_0(A_14162), u1_pre_topc(A_14162)), B_14163) | ~v5_pre_topc(D_14161, A_14162, B_14163) | ~m1_subset_1(D_14161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_14162), u1_pre_topc(A_14162))), u1_struct_0(B_14163)))) | ~v1_funct_2(D_14161, u1_struct_0(g1_pre_topc(u1_struct_0(A_14162), u1_pre_topc(A_14162))), u1_struct_0(B_14163)) | ~m1_subset_1(D_14161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14162), u1_struct_0(B_14163)))) | ~v1_funct_2(D_14161, u1_struct_0(A_14162), u1_struct_0(B_14163)) | ~v1_funct_1(D_14161) | ~l1_pre_topc(B_14163) | ~v2_pre_topc(B_14163) | ~l1_pre_topc(A_14162) | ~v2_pre_topc(A_14162))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.36  tff(c_85228, plain, (![D_14161, B_14163]: (v5_pre_topc(D_14161, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_14163) | ~v5_pre_topc(D_14161, '#skF_3', B_14163) | ~m1_subset_1(D_14161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(B_14163)))) | ~v1_funct_2(D_14161, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_14163)) | ~m1_subset_1(D_14161, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_14163)))) | ~v1_funct_2(D_14161, u1_struct_0('#skF_3'), u1_struct_0(B_14163)) | ~v1_funct_1(D_14161) | ~l1_pre_topc(B_14163) | ~v2_pre_topc(B_14163) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_84416, c_85219])).
% 28.79/18.36  tff(c_96853, plain, (![D_18816, B_18817]: (v5_pre_topc(D_18816, g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), B_18817) | ~v5_pre_topc(D_18816, '#skF_3', B_18817) | ~m1_subset_1(D_18816, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_18817)))) | ~v1_funct_2(D_18816, k1_relat_1('#skF_6'), u1_struct_0(B_18817)) | ~v1_funct_1(D_18816) | ~l1_pre_topc(B_18817) | ~v2_pre_topc(B_18817))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84416, c_84416, c_84570, c_84416, c_84570, c_84416, c_85228])).
% 28.79/18.36  tff(c_96856, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_84572, c_96853])).
% 28.79/18.36  tff(c_96876, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_84574, c_96856])).
% 28.79/18.36  tff(c_96877, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_84424, c_96876])).
% 28.79/18.36  tff(c_96912, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_96877])).
% 28.79/18.36  tff(c_96915, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_96912])).
% 28.79/18.36  tff(c_96919, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_96915])).
% 28.79/18.36  tff(c_96920, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_96877])).
% 28.79/18.36  tff(c_96999, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_96920])).
% 28.79/18.36  tff(c_84426, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_84416, c_107])).
% 28.79/18.36  tff(c_84425, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_84416, c_111])).
% 28.79/18.36  tff(c_85582, plain, (![D_14204, A_14205, B_14206]: (v5_pre_topc(D_14204, A_14205, g1_pre_topc(u1_struct_0(B_14206), u1_pre_topc(B_14206))) | ~v5_pre_topc(D_14204, A_14205, B_14206) | ~m1_subset_1(D_14204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14205), u1_struct_0(g1_pre_topc(u1_struct_0(B_14206), u1_pre_topc(B_14206)))))) | ~v1_funct_2(D_14204, u1_struct_0(A_14205), u1_struct_0(g1_pre_topc(u1_struct_0(B_14206), u1_pre_topc(B_14206)))) | ~m1_subset_1(D_14204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_14205), u1_struct_0(B_14206)))) | ~v1_funct_2(D_14204, u1_struct_0(A_14205), u1_struct_0(B_14206)) | ~v1_funct_1(D_14204) | ~l1_pre_topc(B_14206) | ~v2_pre_topc(B_14206) | ~l1_pre_topc(A_14205) | ~v2_pre_topc(A_14205))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.36  tff(c_85591, plain, (![D_14204, B_14206]: (v5_pre_topc(D_14204, '#skF_3', g1_pre_topc(u1_struct_0(B_14206), u1_pre_topc(B_14206))) | ~v5_pre_topc(D_14204, '#skF_3', B_14206) | ~m1_subset_1(D_14204, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(B_14206), u1_pre_topc(B_14206)))))) | ~v1_funct_2(D_14204, u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_14206), u1_pre_topc(B_14206)))) | ~m1_subset_1(D_14204, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_14206)))) | ~v1_funct_2(D_14204, u1_struct_0('#skF_3'), u1_struct_0(B_14206)) | ~v1_funct_1(D_14204) | ~l1_pre_topc(B_14206) | ~v2_pre_topc(B_14206) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_84416, c_85582])).
% 28.79/18.36  tff(c_101815, plain, (![D_18944, B_18945]: (v5_pre_topc(D_18944, '#skF_3', g1_pre_topc(u1_struct_0(B_18945), u1_pre_topc(B_18945))) | ~v5_pre_topc(D_18944, '#skF_3', B_18945) | ~m1_subset_1(D_18944, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(B_18945), u1_pre_topc(B_18945)))))) | ~v1_funct_2(D_18944, k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(B_18945), u1_pre_topc(B_18945)))) | ~m1_subset_1(D_18944, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_18945)))) | ~v1_funct_2(D_18944, k1_relat_1('#skF_6'), u1_struct_0(B_18945)) | ~v1_funct_1(D_18944) | ~l1_pre_topc(B_18945) | ~v2_pre_topc(B_18945))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_84416, c_84416, c_84416, c_85591])).
% 28.79/18.36  tff(c_101818, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_84572, c_101815])).
% 28.79/18.36  tff(c_101835, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_84, c_84426, c_84425, c_84574, c_82927, c_101818])).
% 28.79/18.36  tff(c_101837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96999, c_101835])).
% 28.79/18.36  tff(c_101838, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_96920])).
% 28.79/18.36  tff(c_101842, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_83193, c_101838])).
% 28.79/18.36  tff(c_101846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_101842])).
% 28.79/18.36  tff(c_101849, plain, (![A_18946]: (~r2_hidden(A_18946, '#skF_6'))), inference(splitRight, [status(thm)], [c_83036])).
% 28.79/18.36  tff(c_101854, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_30, c_101849])).
% 28.79/18.36  tff(c_101882, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_2])).
% 28.79/18.36  tff(c_101879, plain, (![B_5]: (k2_zfmisc_1('#skF_6', B_5)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_101854, c_12])).
% 28.79/18.36  tff(c_101877, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_101854, c_10])).
% 28.79/18.36  tff(c_101848, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_83036])).
% 28.79/18.36  tff(c_101878, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_4])).
% 28.79/18.36  tff(c_102154, plain, (k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_101848, c_101878])).
% 28.79/18.36  tff(c_102381, plain, (![B_18989, A_18990]: (B_18989='#skF_6' | A_18990='#skF_6' | k2_zfmisc_1(A_18990, B_18989)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_101854, c_101854, c_8])).
% 28.79/18.36  tff(c_102395, plain, (u1_struct_0('#skF_4')='#skF_6' | u1_struct_0('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_102154, c_102381])).
% 28.79/18.36  tff(c_102400, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(splitLeft, [status(thm)], [c_102395])).
% 28.79/18.36  tff(c_102405, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_102400, c_82])).
% 28.79/18.36  tff(c_101880, plain, (![A_6]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_14])).
% 28.79/18.36  tff(c_102542, plain, (![B_18997, C_18998, A_18999]: (B_18997='#skF_6' | v1_partfun1(C_18998, A_18999) | ~v1_funct_2(C_18998, A_18999, B_18997) | ~m1_subset_1(C_18998, k1_zfmisc_1(k2_zfmisc_1(A_18999, B_18997))) | ~v1_funct_1(C_18998))), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_58])).
% 28.79/18.36  tff(c_102552, plain, (![B_18997, A_18999]: (B_18997='#skF_6' | v1_partfun1('#skF_6', A_18999) | ~v1_funct_2('#skF_6', A_18999, B_18997) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_101880, c_102542])).
% 28.79/18.36  tff(c_102989, plain, (![B_19038, A_19039]: (B_19038='#skF_6' | v1_partfun1('#skF_6', A_19039) | ~v1_funct_2('#skF_6', A_19039, B_19038))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_102552])).
% 28.79/18.36  tff(c_103007, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_102405, c_102989])).
% 28.79/18.36  tff(c_103012, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_103007])).
% 28.79/18.36  tff(c_101875, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_101854, c_173])).
% 28.79/18.36  tff(c_83116, plain, (![A_13985]: (v4_relat_1(k1_xboole_0, A_13985))), inference(resolution, [status(thm)], [c_14, c_83086])).
% 28.79/18.36  tff(c_101862, plain, (![A_13985]: (v4_relat_1('#skF_6', A_13985))), inference(demodulation, [status(thm), theory('equality')], [c_101854, c_83116])).
% 28.79/18.36  tff(c_102299, plain, (![B_18976, A_18977]: (k1_relat_1(B_18976)=A_18977 | ~v1_partfun1(B_18976, A_18977) | ~v4_relat_1(B_18976, A_18977) | ~v1_relat_1(B_18976))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.36  tff(c_102302, plain, (![A_13985]: (k1_relat_1('#skF_6')=A_13985 | ~v1_partfun1('#skF_6', A_13985) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_101862, c_102299])).
% 28.79/18.36  tff(c_102308, plain, (![A_13985]: (A_13985='#skF_6' | ~v1_partfun1('#skF_6', A_13985))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_101875, c_102302])).
% 28.79/18.36  tff(c_103016, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_103012, c_102308])).
% 28.79/18.36  tff(c_102402, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_102400, c_83183])).
% 28.79/18.36  tff(c_103018, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_103016, c_102402])).
% 28.79/18.36  tff(c_103023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101882, c_101879, c_103018])).
% 28.79/18.36  tff(c_103024, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_103007])).
% 28.79/18.36  tff(c_103026, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_103024, c_102402])).
% 28.79/18.36  tff(c_103031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101882, c_101877, c_103026])).
% 28.79/18.36  tff(c_103032, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_102395])).
% 28.79/18.36  tff(c_102124, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_6, c_83183])).
% 28.79/18.36  tff(c_103035, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_103032, c_102124])).
% 28.79/18.36  tff(c_103039, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_103032, c_82])).
% 28.79/18.36  tff(c_103167, plain, (![C_19045, A_19046, B_19047]: (v1_partfun1(C_19045, A_19046) | ~v1_funct_2(C_19045, A_19046, B_19047) | ~v1_funct_1(C_19045) | ~m1_subset_1(C_19045, k1_zfmisc_1(k2_zfmisc_1(A_19046, B_19047))) | v1_xboole_0(B_19047))), inference(cnfTransformation, [status(thm)], [f_103])).
% 28.79/18.36  tff(c_103177, plain, (![A_19046, B_19047]: (v1_partfun1('#skF_6', A_19046) | ~v1_funct_2('#skF_6', A_19046, B_19047) | ~v1_funct_1('#skF_6') | v1_xboole_0(B_19047))), inference(resolution, [status(thm)], [c_101880, c_103167])).
% 28.79/18.36  tff(c_103692, plain, (![A_19097, B_19098]: (v1_partfun1('#skF_6', A_19097) | ~v1_funct_2('#skF_6', A_19097, B_19098) | v1_xboole_0(B_19098))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_103177])).
% 28.79/18.36  tff(c_103701, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_103039, c_103692])).
% 28.79/18.36  tff(c_103712, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_103035, c_103701])).
% 28.79/18.36  tff(c_103720, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_103712, c_102308])).
% 28.79/18.36  tff(c_103036, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_103032, c_83183])).
% 28.79/18.36  tff(c_103723, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_103720, c_103036])).
% 28.79/18.36  tff(c_103728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101882, c_101879, c_103723])).
% 28.79/18.36  tff(c_103731, plain, (![A_19099]: (~r2_hidden(A_19099, '#skF_6'))), inference(splitRight, [status(thm)], [c_83037])).
% 28.79/18.36  tff(c_103736, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_30, c_103731])).
% 28.79/18.36  tff(c_83018, plain, (![A_13979, A_4]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_13979, '#skF_2'(A_4, k1_xboole_0)))), inference(resolution, [status(thm)], [c_380, c_83016])).
% 28.79/18.36  tff(c_83121, plain, (![A_13990, A_13991]: (~r2_hidden(A_13990, '#skF_2'(A_13991, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_83018])).
% 28.79/18.36  tff(c_83133, plain, (![A_13992]: ('#skF_2'(A_13992, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_83121])).
% 28.79/18.36  tff(c_83144, plain, (![A_13992]: (v1_funct_2(k1_xboole_0, A_13992, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_83133, c_44])).
% 28.79/18.36  tff(c_103739, plain, (![A_13992]: (v1_funct_2('#skF_6', A_13992, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_83144])).
% 28.79/18.36  tff(c_83129, plain, (![A_13991]: ('#skF_2'(A_13991, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_83121])).
% 28.79/18.36  tff(c_103740, plain, (![A_13991]: ('#skF_2'(A_13991, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_83129])).
% 28.79/18.36  tff(c_83020, plain, (![A_13979, B_5]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_13979, '#skF_2'(k1_xboole_0, B_5)))), inference(resolution, [status(thm)], [c_383, c_83016])).
% 28.79/18.36  tff(c_83047, plain, (![A_13981, B_13982]: (~r2_hidden(A_13981, '#skF_2'(k1_xboole_0, B_13982)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_83020])).
% 28.79/18.36  tff(c_83056, plain, (![B_13983]: ('#skF_2'(k1_xboole_0, B_13983)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_83047])).
% 28.79/18.36  tff(c_83067, plain, (![B_13983]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_13983))), inference(superposition, [status(thm), theory('equality')], [c_83056, c_44])).
% 28.79/18.36  tff(c_103741, plain, (![B_13983]: (v1_funct_2('#skF_6', '#skF_6', B_13983))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_83067])).
% 28.79/18.36  tff(c_83052, plain, (![B_13982]: ('#skF_2'(k1_xboole_0, B_13982)=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_83047])).
% 28.79/18.36  tff(c_103744, plain, (![B_13982]: ('#skF_2'('#skF_6', B_13982)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_83052])).
% 28.79/18.36  tff(c_103761, plain, (![A_6]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_14])).
% 28.79/18.36  tff(c_126126, plain, (![B_20374, C_20375, A_20376]: (B_20374='#skF_6' | v1_partfun1(C_20375, A_20376) | ~v1_funct_2(C_20375, A_20376, B_20374) | ~m1_subset_1(C_20375, k1_zfmisc_1(k2_zfmisc_1(A_20376, B_20374))) | ~v1_funct_1(C_20375))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_58])).
% 28.79/18.36  tff(c_126139, plain, (![B_20374, A_20376]: (B_20374='#skF_6' | v1_partfun1('#skF_6', A_20376) | ~v1_funct_2('#skF_6', A_20376, B_20374) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_103761, c_126126])).
% 28.79/18.36  tff(c_126280, plain, (![B_20385, A_20386]: (B_20385='#skF_6' | v1_partfun1('#skF_6', A_20386) | ~v1_funct_2('#skF_6', A_20386, B_20385))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_126139])).
% 28.79/18.36  tff(c_126302, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_126280])).
% 28.79/18.36  tff(c_126303, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_126302])).
% 28.79/18.36  tff(c_103756, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_173])).
% 28.79/18.36  tff(c_103743, plain, (![A_13985]: (v4_relat_1('#skF_6', A_13985))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_83116])).
% 28.79/18.36  tff(c_104394, plain, (![B_19150, A_19151]: (k1_relat_1(B_19150)=A_19151 | ~v1_partfun1(B_19150, A_19151) | ~v4_relat_1(B_19150, A_19151) | ~v1_relat_1(B_19150))), inference(cnfTransformation, [status(thm)], [f_111])).
% 28.79/18.36  tff(c_104397, plain, (![A_13985]: (k1_relat_1('#skF_6')=A_13985 | ~v1_partfun1('#skF_6', A_13985) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_103743, c_104394])).
% 28.79/18.36  tff(c_104403, plain, (![A_13985]: (A_13985='#skF_6' | ~v1_partfun1('#skF_6', A_13985))), inference(demodulation, [status(thm), theory('equality')], [c_368, c_103756, c_104397])).
% 28.79/18.36  tff(c_126307, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_126303, c_104403])).
% 28.79/18.36  tff(c_131097, plain, (![D_20667, A_20668, B_20669]: (v5_pre_topc(D_20667, A_20668, g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669))) | ~v5_pre_topc(D_20667, A_20668, B_20669) | ~m1_subset_1(D_20667, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))))) | ~v1_funct_2(D_20667, u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))) | ~m1_subset_1(D_20667, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20668), u1_struct_0(B_20669)))) | ~v1_funct_2(D_20667, u1_struct_0(A_20668), u1_struct_0(B_20669)) | ~v1_funct_1(D_20667) | ~l1_pre_topc(B_20669) | ~v2_pre_topc(B_20669) | ~l1_pre_topc(A_20668) | ~v2_pre_topc(A_20668))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.36  tff(c_131120, plain, (![A_20668, B_20669]: (v5_pre_topc('#skF_2'(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))), A_20668, g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))), A_20668, B_20669) | ~v1_funct_2('#skF_2'(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))), u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20668), u1_struct_0(B_20669)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669)))), u1_struct_0(A_20668), u1_struct_0(B_20669)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_20668), u1_struct_0(g1_pre_topc(u1_struct_0(B_20669), u1_pre_topc(B_20669))))) | ~l1_pre_topc(B_20669) | ~v2_pre_topc(B_20669) | ~l1_pre_topc(A_20668) | ~v2_pre_topc(A_20668))), inference(resolution, [status(thm)], [c_54, c_131097])).
% 28.79/18.36  tff(c_131838, plain, (![A_20744, B_20745]: (v5_pre_topc('#skF_2'(u1_struct_0(A_20744), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), A_20744, g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_20744), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), A_20744, B_20745) | ~m1_subset_1('#skF_2'(u1_struct_0(A_20744), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20744), u1_struct_0(B_20745)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_20744), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), u1_struct_0(A_20744), u1_struct_0(B_20745)) | ~l1_pre_topc(B_20745) | ~v2_pre_topc(B_20745) | ~l1_pre_topc(A_20744) | ~v2_pre_topc(A_20744))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_131120])).
% 28.79/18.36  tff(c_131844, plain, (![B_20745]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), '#skF_3', g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745))) | ~v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), '#skF_3', B_20745) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0(B_20745)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745)))), u1_struct_0('#skF_3'), u1_struct_0(B_20745)) | ~l1_pre_topc(B_20745) | ~v2_pre_topc(B_20745) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_126307, c_131838])).
% 28.79/18.36  tff(c_131862, plain, (![B_20745]: (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_20745), u1_pre_topc(B_20745))) | ~v5_pre_topc('#skF_6', '#skF_3', B_20745) | ~l1_pre_topc(B_20745) | ~v2_pre_topc(B_20745))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_103741, c_103744, c_126307, c_126307, c_103761, c_103744, c_126307, c_103744, c_126307, c_103744, c_126307, c_131844])).
% 28.79/18.36  tff(c_126310, plain, (~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_126307, c_83015])).
% 28.79/18.36  tff(c_103885, plain, (![A_19110]: (m1_subset_1(u1_pre_topc(A_19110), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_19110)))) | ~l1_pre_topc(A_19110))), inference(cnfTransformation, [status(thm)], [f_151])).
% 28.79/18.36  tff(c_103894, plain, (![A_19110]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_19110), u1_pre_topc(A_19110))) | ~l1_pre_topc(A_19110))), inference(resolution, [status(thm)], [c_103885, c_60])).
% 28.79/18.36  tff(c_105031, plain, (![B_19221, C_19222, A_19223]: (B_19221='#skF_6' | v1_partfun1(C_19222, A_19223) | ~v1_funct_2(C_19222, A_19223, B_19221) | ~m1_subset_1(C_19222, k1_zfmisc_1(k2_zfmisc_1(A_19223, B_19221))) | ~v1_funct_1(C_19222))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_58])).
% 28.79/18.36  tff(c_105044, plain, (![B_19221, A_19223]: (B_19221='#skF_6' | v1_partfun1('#skF_6', A_19223) | ~v1_funct_2('#skF_6', A_19223, B_19221) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_103761, c_105031])).
% 28.79/18.36  tff(c_105195, plain, (![B_19232, A_19233]: (B_19232='#skF_6' | v1_partfun1('#skF_6', A_19233) | ~v1_funct_2('#skF_6', A_19233, B_19232))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_105044])).
% 28.79/18.36  tff(c_105217, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_107, c_105195])).
% 28.79/18.36  tff(c_105218, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_105217])).
% 28.79/18.36  tff(c_105222, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_105218, c_104403])).
% 28.79/18.36  tff(c_105436, plain, (![D_19241, A_19242, B_19243]: (v5_pre_topc(D_19241, A_19242, g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243))) | ~v5_pre_topc(D_19241, A_19242, B_19243) | ~m1_subset_1(D_19241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))))) | ~v1_funct_2(D_19241, u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))) | ~m1_subset_1(D_19241, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19242), u1_struct_0(B_19243)))) | ~v1_funct_2(D_19241, u1_struct_0(A_19242), u1_struct_0(B_19243)) | ~v1_funct_1(D_19241) | ~l1_pre_topc(B_19243) | ~v2_pre_topc(B_19243) | ~l1_pre_topc(A_19242) | ~v2_pre_topc(A_19242))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.36  tff(c_105456, plain, (![A_19242, B_19243]: (v5_pre_topc('#skF_2'(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))), A_19242, g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))), A_19242, B_19243) | ~v1_funct_2('#skF_2'(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))), u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19242), u1_struct_0(B_19243)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243)))), u1_struct_0(A_19242), u1_struct_0(B_19243)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_19242), u1_struct_0(g1_pre_topc(u1_struct_0(B_19243), u1_pre_topc(B_19243))))) | ~l1_pre_topc(B_19243) | ~v2_pre_topc(B_19243) | ~l1_pre_topc(A_19242) | ~v2_pre_topc(A_19242))), inference(resolution, [status(thm)], [c_54, c_105436])).
% 28.79/18.36  tff(c_112511, plain, (![A_19648, B_19649]: (v5_pre_topc('#skF_2'(u1_struct_0(A_19648), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), A_19648, g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_19648), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), A_19648, B_19649) | ~m1_subset_1('#skF_2'(u1_struct_0(A_19648), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19648), u1_struct_0(B_19649)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_19648), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), u1_struct_0(A_19648), u1_struct_0(B_19649)) | ~l1_pre_topc(B_19649) | ~v2_pre_topc(B_19649) | ~l1_pre_topc(A_19648) | ~v2_pre_topc(A_19648))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_105456])).
% 28.79/18.36  tff(c_112521, plain, (![B_19649]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), '#skF_3', g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649))) | ~v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), '#skF_3', B_19649) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_19649)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_19649), u1_pre_topc(B_19649)))), u1_struct_0('#skF_3'), u1_struct_0(B_19649)) | ~l1_pre_topc(B_19649) | ~v2_pre_topc(B_19649) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105222, c_112511])).
% 28.79/18.36  tff(c_114938, plain, (![B_19759]: (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_19759), u1_pre_topc(B_19759))) | ~v5_pre_topc('#skF_6', '#skF_3', B_19759) | ~l1_pre_topc(B_19759) | ~v2_pre_topc(B_19759))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_103741, c_103744, c_105222, c_105222, c_103761, c_103744, c_105222, c_103744, c_105222, c_103744, c_105222, c_112521])).
% 28.79/18.36  tff(c_103730, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitRight, [status(thm)], [c_83037])).
% 28.79/18.36  tff(c_103759, plain, (![A_1]: (A_1='#skF_6' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_4])).
% 28.79/18.36  tff(c_104103, plain, (k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))='#skF_6'), inference(resolution, [status(thm)], [c_103730, c_103759])).
% 28.79/18.36  tff(c_104314, plain, (![B_19141, A_19142]: (B_19141='#skF_6' | A_19142='#skF_6' | k2_zfmisc_1(A_19142, B_19141)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_103736, c_8])).
% 28.79/18.36  tff(c_104330, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_104103, c_104314])).
% 28.79/18.36  tff(c_104741, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(splitLeft, [status(thm)], [c_104330])).
% 28.79/18.36  tff(c_105224, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_105222, c_104741])).
% 28.79/18.36  tff(c_111664, plain, (![D_19565, A_19566, B_19567]: (v5_pre_topc(D_19565, g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566)), B_19567) | ~v5_pre_topc(D_19565, A_19566, B_19567) | ~m1_subset_1(D_19565, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)))) | ~v1_funct_2(D_19565, u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)) | ~m1_subset_1(D_19565, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19566), u1_struct_0(B_19567)))) | ~v1_funct_2(D_19565, u1_struct_0(A_19566), u1_struct_0(B_19567)) | ~v1_funct_1(D_19565) | ~l1_pre_topc(B_19567) | ~v2_pre_topc(B_19567) | ~l1_pre_topc(A_19566) | ~v2_pre_topc(A_19566))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.36  tff(c_111684, plain, (![A_19566, B_19567]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)), g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566)), B_19567) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)), A_19566, B_19567) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)), u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19566), u1_struct_0(B_19567)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567)), u1_struct_0(A_19566), u1_struct_0(B_19567)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19566), u1_pre_topc(A_19566))), u1_struct_0(B_19567))) | ~l1_pre_topc(B_19567) | ~v2_pre_topc(B_19567) | ~l1_pre_topc(A_19566) | ~v2_pre_topc(A_19566))), inference(resolution, [status(thm)], [c_54, c_111664])).
% 28.79/18.36  tff(c_112091, plain, (![A_19625, B_19626]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625), u1_pre_topc(A_19625))), u1_struct_0(B_19626)), g1_pre_topc(u1_struct_0(A_19625), u1_pre_topc(A_19625)), B_19626) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625), u1_pre_topc(A_19625))), u1_struct_0(B_19626)), A_19625, B_19626) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625), u1_pre_topc(A_19625))), u1_struct_0(B_19626)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19625), u1_struct_0(B_19626)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_19625), u1_pre_topc(A_19625))), u1_struct_0(B_19626)), u1_struct_0(A_19625), u1_struct_0(B_19626)) | ~l1_pre_topc(B_19626) | ~v2_pre_topc(B_19626) | ~l1_pre_topc(A_19625) | ~v2_pre_topc(A_19625))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_111684])).
% 28.79/18.36  tff(c_112105, plain, (![B_19626]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_19626)), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_19626) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_19626)), '#skF_3', B_19626) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_19626)), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0(B_19626)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_19626)), u1_struct_0('#skF_3'), u1_struct_0(B_19626)) | ~l1_pre_topc(B_19626) | ~v2_pre_topc(B_19626) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_105222, c_112091])).
% 28.79/18.36  tff(c_112232, plain, (![B_19635]: (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_19635) | ~v5_pre_topc('#skF_6', '#skF_3', B_19635) | ~l1_pre_topc(B_19635) | ~v2_pre_topc(B_19635))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_103741, c_103744, c_105222, c_105224, c_105222, c_103761, c_103744, c_105224, c_105222, c_103744, c_105224, c_105222, c_103744, c_105222, c_105224, c_105222, c_112105])).
% 28.79/18.36  tff(c_105225, plain, (~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_105222, c_83015])).
% 28.79/18.36  tff(c_112247, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_112232, c_105225])).
% 28.79/18.36  tff(c_112707, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_112247])).
% 28.79/18.36  tff(c_112710, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_112707])).
% 28.79/18.36  tff(c_112714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_112710])).
% 28.79/18.36  tff(c_112715, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_112247])).
% 28.79/18.36  tff(c_112812, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_112715])).
% 28.79/18.36  tff(c_114941, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_114938, c_112812])).
% 28.79/18.36  tff(c_114954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82927, c_114941])).
% 28.79/18.36  tff(c_114955, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_112715])).
% 28.79/18.36  tff(c_114959, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_103894, c_114955])).
% 28.79/18.36  tff(c_114963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_114959])).
% 28.79/18.36  tff(c_114964, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_105217])).
% 28.79/18.36  tff(c_103758, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_103736, c_103736, c_10])).
% 28.79/18.36  tff(c_122070, plain, (![D_20108, A_20109, B_20110]: (v5_pre_topc(D_20108, g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109)), B_20110) | ~v5_pre_topc(D_20108, A_20109, B_20110) | ~m1_subset_1(D_20108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)))) | ~v1_funct_2(D_20108, u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)) | ~m1_subset_1(D_20108, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20109), u1_struct_0(B_20110)))) | ~v1_funct_2(D_20108, u1_struct_0(A_20109), u1_struct_0(B_20110)) | ~v1_funct_1(D_20108) | ~l1_pre_topc(B_20110) | ~v2_pre_topc(B_20110) | ~l1_pre_topc(A_20109) | ~v2_pre_topc(A_20109))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.36  tff(c_122093, plain, (![A_20109, B_20110]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)), g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109)), B_20110) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)), A_20109, B_20110) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)), u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20109), u1_struct_0(B_20110)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110)), u1_struct_0(A_20109), u1_struct_0(B_20110)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20109), u1_pre_topc(A_20109))), u1_struct_0(B_20110))) | ~l1_pre_topc(B_20110) | ~v2_pre_topc(B_20110) | ~l1_pre_topc(A_20109) | ~v2_pre_topc(A_20109))), inference(resolution, [status(thm)], [c_54, c_122070])).
% 28.79/18.36  tff(c_123380, plain, (![A_20214, B_20215]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0(B_20215)), g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214)), B_20215) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0(B_20215)), A_20214, B_20215) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0(B_20215)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20214), u1_struct_0(B_20215)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0(B_20215)), u1_struct_0(A_20214), u1_struct_0(B_20215)) | ~l1_pre_topc(B_20215) | ~v2_pre_topc(B_20215) | ~l1_pre_topc(A_20214) | ~v2_pre_topc(A_20214))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_122093])).
% 28.79/18.36  tff(c_123388, plain, (![A_20214]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0('#skF_4')), g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214)), '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0('#skF_4')), A_20214, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20214), '#skF_6'))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214))), u1_struct_0('#skF_4')), u1_struct_0(A_20214), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_20214) | ~v2_pre_topc(A_20214))), inference(superposition, [status(thm), theory('equality')], [c_114964, c_123380])).
% 28.79/18.36  tff(c_123406, plain, (![A_20214]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_20214), u1_pre_topc(A_20214)), '#skF_4') | ~v5_pre_topc('#skF_6', A_20214, '#skF_4') | ~l1_pre_topc(A_20214) | ~v2_pre_topc(A_20214))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_103739, c_103740, c_114964, c_114964, c_103761, c_103758, c_103740, c_114964, c_103740, c_114964, c_103740, c_114964, c_123388])).
% 28.79/18.36  tff(c_114966, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_114964, c_83015])).
% 28.79/18.36  tff(c_115164, plain, (![D_19769, A_19770, B_19771]: (v5_pre_topc(D_19769, A_19770, g1_pre_topc(u1_struct_0(B_19771), u1_pre_topc(B_19771))) | ~v5_pre_topc(D_19769, A_19770, B_19771) | ~m1_subset_1(D_19769, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19770), u1_struct_0(g1_pre_topc(u1_struct_0(B_19771), u1_pre_topc(B_19771)))))) | ~v1_funct_2(D_19769, u1_struct_0(A_19770), u1_struct_0(g1_pre_topc(u1_struct_0(B_19771), u1_pre_topc(B_19771)))) | ~m1_subset_1(D_19769, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19770), u1_struct_0(B_19771)))) | ~v1_funct_2(D_19769, u1_struct_0(A_19770), u1_struct_0(B_19771)) | ~v1_funct_1(D_19769) | ~l1_pre_topc(B_19771) | ~v2_pre_topc(B_19771) | ~l1_pre_topc(A_19770) | ~v2_pre_topc(A_19770))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.36  tff(c_115183, plain, (![A_19770, B_19771]: (v5_pre_topc('#skF_6', A_19770, g1_pre_topc(u1_struct_0(B_19771), u1_pre_topc(B_19771))) | ~v5_pre_topc('#skF_6', A_19770, B_19771) | ~v1_funct_2('#skF_6', u1_struct_0(A_19770), u1_struct_0(g1_pre_topc(u1_struct_0(B_19771), u1_pre_topc(B_19771)))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_19770), u1_struct_0(B_19771)))) | ~v1_funct_2('#skF_6', u1_struct_0(A_19770), u1_struct_0(B_19771)) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(B_19771) | ~v2_pre_topc(B_19771) | ~l1_pre_topc(A_19770) | ~v2_pre_topc(A_19770))), inference(resolution, [status(thm)], [c_103761, c_115164])).
% 28.79/18.36  tff(c_125314, plain, (![A_20310, B_20311]: (v5_pre_topc('#skF_6', A_20310, g1_pre_topc(u1_struct_0(B_20311), u1_pre_topc(B_20311))) | ~v5_pre_topc('#skF_6', A_20310, B_20311) | ~v1_funct_2('#skF_6', u1_struct_0(A_20310), u1_struct_0(g1_pre_topc(u1_struct_0(B_20311), u1_pre_topc(B_20311)))) | ~v1_funct_2('#skF_6', u1_struct_0(A_20310), u1_struct_0(B_20311)) | ~l1_pre_topc(B_20311) | ~v2_pre_topc(B_20311) | ~l1_pre_topc(A_20310) | ~v2_pre_topc(A_20310))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_103761, c_115183])).
% 28.79/18.36  tff(c_125323, plain, (![A_20310]: (v5_pre_topc('#skF_6', A_20310, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_20310, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_20310), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(A_20310), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_20310) | ~v2_pre_topc(A_20310))), inference(superposition, [status(thm), theory('equality')], [c_114964, c_125314])).
% 28.79/18.36  tff(c_125394, plain, (![A_20314]: (v5_pre_topc('#skF_6', A_20314, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_20314, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_20314), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~l1_pre_topc(A_20314) | ~v2_pre_topc(A_20314))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_103739, c_114964, c_114964, c_125323])).
% 28.79/18.36  tff(c_125403, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v1_funct_2('#skF_6', '#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_104741, c_125394])).
% 28.79/18.36  tff(c_125409, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_103741, c_125403])).
% 28.79/18.36  tff(c_125410, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_114966, c_125409])).
% 28.79/18.36  tff(c_125638, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_125410])).
% 28.79/18.36  tff(c_125641, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_125638])).
% 28.79/18.36  tff(c_125645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_125641])).
% 28.79/18.36  tff(c_125646, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_125410])).
% 28.79/18.36  tff(c_125901, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_125646])).
% 28.79/18.36  tff(c_125904, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_123406, c_125901])).
% 28.79/18.36  tff(c_125908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_82927, c_125904])).
% 28.79/18.36  tff(c_125909, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_125646])).
% 28.79/18.36  tff(c_125913, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_103894, c_125909])).
% 28.79/18.36  tff(c_125917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_125913])).
% 28.79/18.36  tff(c_125918, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_104330])).
% 28.79/18.36  tff(c_125930, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_125918, c_103894])).
% 28.79/18.36  tff(c_131182, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_125930])).
% 28.79/18.36  tff(c_131240, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_103894, c_131182])).
% 28.79/18.36  tff(c_131244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_131240])).
% 28.79/18.36  tff(c_131246, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_125930])).
% 28.79/18.36  tff(c_62, plain, (![A_47, B_48]: (v1_pre_topc(g1_pre_topc(A_47, B_48)) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_147])).
% 28.79/18.36  tff(c_103896, plain, (![A_19110]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_19110), u1_pre_topc(A_19110))) | ~l1_pre_topc(A_19110))), inference(resolution, [status(thm)], [c_103885, c_62])).
% 28.79/18.36  tff(c_125927, plain, (v1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_125918, c_103896])).
% 28.79/18.36  tff(c_131263, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_125927])).
% 28.79/18.36  tff(c_131266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131246, c_131263])).
% 28.79/18.36  tff(c_131268, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_125927])).
% 28.79/18.36  tff(c_125933, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_125918, c_66])).
% 28.79/18.36  tff(c_134127, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_131268, c_125933])).
% 28.79/18.36  tff(c_134128, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_134127])).
% 28.79/18.36  tff(c_134131, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_66, c_134128])).
% 28.79/18.36  tff(c_134135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_134131])).
% 28.79/18.36  tff(c_134137, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_134127])).
% 28.79/18.36  tff(c_131269, plain, (![D_20683, A_20684, B_20685]: (v5_pre_topc(D_20683, g1_pre_topc(u1_struct_0(A_20684), u1_pre_topc(A_20684)), B_20685) | ~v5_pre_topc(D_20683, A_20684, B_20685) | ~m1_subset_1(D_20683, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_20684), u1_pre_topc(A_20684))), u1_struct_0(B_20685)))) | ~v1_funct_2(D_20683, u1_struct_0(g1_pre_topc(u1_struct_0(A_20684), u1_pre_topc(A_20684))), u1_struct_0(B_20685)) | ~m1_subset_1(D_20683, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20684), u1_struct_0(B_20685)))) | ~v1_funct_2(D_20683, u1_struct_0(A_20684), u1_struct_0(B_20685)) | ~v1_funct_1(D_20683) | ~l1_pre_topc(B_20685) | ~v2_pre_topc(B_20685) | ~l1_pre_topc(A_20684) | ~v2_pre_topc(A_20684))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.36  tff(c_131288, plain, (![A_20684, B_20685]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_20684), u1_pre_topc(A_20684)), B_20685) | ~v5_pre_topc('#skF_6', A_20684, B_20685) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_20684), u1_pre_topc(A_20684))), u1_struct_0(B_20685)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20684), u1_struct_0(B_20685)))) | ~v1_funct_2('#skF_6', u1_struct_0(A_20684), u1_struct_0(B_20685)) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(B_20685) | ~v2_pre_topc(B_20685) | ~l1_pre_topc(A_20684) | ~v2_pre_topc(A_20684))), inference(resolution, [status(thm)], [c_103761, c_131269])).
% 28.79/18.36  tff(c_134612, plain, (![A_20888, B_20889]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_20888), u1_pre_topc(A_20888)), B_20889) | ~v5_pre_topc('#skF_6', A_20888, B_20889) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_20888), u1_pre_topc(A_20888))), u1_struct_0(B_20889)) | ~v1_funct_2('#skF_6', u1_struct_0(A_20888), u1_struct_0(B_20889)) | ~l1_pre_topc(B_20889) | ~v2_pre_topc(B_20889) | ~l1_pre_topc(A_20888) | ~v2_pre_topc(A_20888))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_103761, c_131288])).
% 28.79/18.36  tff(c_134618, plain, (![B_20889]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_20889) | ~v5_pre_topc('#skF_6', '#skF_3', B_20889) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(B_20889)) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0(B_20889)) | ~l1_pre_topc(B_20889) | ~v2_pre_topc(B_20889) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_126307, c_134612])).
% 28.79/18.36  tff(c_135033, plain, (![B_20924]: (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_20924) | ~v5_pre_topc('#skF_6', '#skF_3', B_20924) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(B_20924)) | ~l1_pre_topc(B_20924) | ~v2_pre_topc(B_20924))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_103741, c_126307, c_126307, c_134618])).
% 28.79/18.36  tff(c_135042, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_125918, c_135033])).
% 28.79/18.36  tff(c_135048, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_134137, c_131268, c_103739, c_135042])).
% 28.79/18.36  tff(c_135049, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_126310, c_135048])).
% 28.79/18.36  tff(c_135052, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_131862, c_135049])).
% 28.79/18.36  tff(c_135056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82927, c_135052])).
% 28.79/18.36  tff(c_135057, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_126302])).
% 28.79/18.36  tff(c_135383, plain, (![D_20944, A_20945, B_20946]: (v5_pre_topc(D_20944, g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945)), B_20946) | ~v5_pre_topc(D_20944, A_20945, B_20946) | ~m1_subset_1(D_20944, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)))) | ~v1_funct_2(D_20944, u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)) | ~m1_subset_1(D_20944, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20945), u1_struct_0(B_20946)))) | ~v1_funct_2(D_20944, u1_struct_0(A_20945), u1_struct_0(B_20946)) | ~v1_funct_1(D_20944) | ~l1_pre_topc(B_20946) | ~v2_pre_topc(B_20946) | ~l1_pre_topc(A_20945) | ~v2_pre_topc(A_20945))), inference(cnfTransformation, [status(thm)], [f_188])).
% 28.79/18.36  tff(c_135403, plain, (![A_20945, B_20946]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)), g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945)), B_20946) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)), A_20945, B_20946) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)), u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_20945), u1_struct_0(B_20946)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946)), u1_struct_0(A_20945), u1_struct_0(B_20946)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_20945), u1_pre_topc(A_20945))), u1_struct_0(B_20946))) | ~l1_pre_topc(B_20946) | ~v2_pre_topc(B_20946) | ~l1_pre_topc(A_20945) | ~v2_pre_topc(A_20945))), inference(resolution, [status(thm)], [c_54, c_135383])).
% 28.79/18.36  tff(c_144681, plain, (![A_22263, B_22264]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0(B_22264)), g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263)), B_22264) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0(B_22264)), A_22263, B_22264) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0(B_22264)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22263), u1_struct_0(B_22264)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0(B_22264)), u1_struct_0(A_22263), u1_struct_0(B_22264)) | ~l1_pre_topc(B_22264) | ~v2_pre_topc(B_22264) | ~l1_pre_topc(A_22263) | ~v2_pre_topc(A_22263))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_135403])).
% 28.79/18.36  tff(c_144697, plain, (![A_22263]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0('#skF_4')), g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263)), '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0('#skF_4')), A_22263, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22263), '#skF_6'))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_22263), u1_pre_topc(A_22263))), u1_struct_0('#skF_4')), u1_struct_0(A_22263), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_22263) | ~v2_pre_topc(A_22263))), inference(superposition, [status(thm), theory('equality')], [c_135057, c_144681])).
% 28.79/18.36  tff(c_147729, plain, (![A_22434]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_22434), u1_pre_topc(A_22434)), '#skF_4') | ~v5_pre_topc('#skF_6', A_22434, '#skF_4') | ~l1_pre_topc(A_22434) | ~v2_pre_topc(A_22434))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_103739, c_103740, c_135057, c_135057, c_103761, c_103758, c_103740, c_135057, c_103740, c_135057, c_103740, c_135057, c_144697])).
% 28.79/18.36  tff(c_135059, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_135057, c_125918])).
% 28.79/18.36  tff(c_144323, plain, (![D_22227, A_22228, B_22229]: (v5_pre_topc(D_22227, A_22228, g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229))) | ~v5_pre_topc(D_22227, A_22228, B_22229) | ~m1_subset_1(D_22227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))))) | ~v1_funct_2(D_22227, u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))) | ~m1_subset_1(D_22227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228), u1_struct_0(B_22229)))) | ~v1_funct_2(D_22227, u1_struct_0(A_22228), u1_struct_0(B_22229)) | ~v1_funct_1(D_22227) | ~l1_pre_topc(B_22229) | ~v2_pre_topc(B_22229) | ~l1_pre_topc(A_22228) | ~v2_pre_topc(A_22228))), inference(cnfTransformation, [status(thm)], [f_217])).
% 28.79/18.36  tff(c_144335, plain, (![D_22227, A_22228]: (v5_pre_topc(D_22227, A_22228, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc(D_22227, A_22228, '#skF_4') | ~m1_subset_1(D_22227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))) | ~v1_funct_2(D_22227, u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1(D_22227, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_22227, u1_struct_0(A_22228), u1_struct_0('#skF_4')) | ~v1_funct_1(D_22227) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_22228) | ~v2_pre_topc(A_22228))), inference(superposition, [status(thm), theory('equality')], [c_135057, c_144323])).
% 28.79/18.36  tff(c_144376, plain, (![D_22230, A_22231]: (v5_pre_topc(D_22230, A_22231, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc(D_22230, A_22231, '#skF_4') | ~m1_subset_1(D_22230, k1_zfmisc_1('#skF_6')) | ~v1_funct_2(D_22230, u1_struct_0(A_22231), '#skF_6') | ~v1_funct_1(D_22230) | ~l1_pre_topc(A_22231) | ~v2_pre_topc(A_22231))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_135057, c_103758, c_135057, c_135059, c_135057, c_103758, c_135059, c_135057, c_144335])).
% 28.79/18.36  tff(c_135060, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_135057, c_83015])).
% 28.79/18.36  tff(c_144379, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_144376, c_135060])).
% 28.79/18.36  tff(c_144382, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_103739, c_103761, c_144379])).
% 28.79/18.36  tff(c_144468, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_144382])).
% 28.79/18.36  tff(c_144471, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_144468])).
% 28.79/18.36  tff(c_144475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_144471])).
% 28.79/18.36  tff(c_144477, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_144382])).
% 28.79/18.36  tff(c_144343, plain, (![A_22228, B_22229]: (v5_pre_topc('#skF_2'(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))), A_22228, g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))), A_22228, B_22229) | ~v1_funct_2('#skF_2'(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))), u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22228), u1_struct_0(B_22229)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229)))), u1_struct_0(A_22228), u1_struct_0(B_22229)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_22228), u1_struct_0(g1_pre_topc(u1_struct_0(B_22229), u1_pre_topc(B_22229))))) | ~l1_pre_topc(B_22229) | ~v2_pre_topc(B_22229) | ~l1_pre_topc(A_22228) | ~v2_pre_topc(A_22228))), inference(resolution, [status(thm)], [c_54, c_144323])).
% 28.79/18.36  tff(c_144919, plain, (![A_22291, B_22292]: (v5_pre_topc('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0(B_22292), u1_pre_topc(B_22292)))), A_22291, g1_pre_topc(u1_struct_0(B_22292), u1_pre_topc(B_22292))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0(B_22292), u1_pre_topc(B_22292)))), A_22291, B_22292) | ~m1_subset_1('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0(B_22292), u1_pre_topc(B_22292)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22291), u1_struct_0(B_22292)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0(B_22292), u1_pre_topc(B_22292)))), u1_struct_0(A_22291), u1_struct_0(B_22292)) | ~l1_pre_topc(B_22292) | ~v2_pre_topc(B_22292) | ~l1_pre_topc(A_22291) | ~v2_pre_topc(A_22291))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_144343])).
% 28.79/18.36  tff(c_144935, plain, (![A_22291]: (v5_pre_topc('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_22291, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_22291, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_22291), '#skF_6'))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_22291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_22291), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_22291) | ~v2_pre_topc(A_22291))), inference(superposition, [status(thm), theory('equality')], [c_135057, c_144919])).
% 28.79/18.36  tff(c_146805, plain, (![A_22381]: (v5_pre_topc('#skF_6', A_22381, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_22381, '#skF_4') | ~l1_pre_topc(A_22381) | ~v2_pre_topc(A_22381))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_103739, c_103740, c_135057, c_135059, c_135057, c_103761, c_103758, c_103740, c_135059, c_135057, c_103740, c_135059, c_135057, c_103740, c_135057, c_135059, c_135057, c_144935])).
% 28.79/18.36  tff(c_146815, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_146805, c_135060])).
% 28.79/18.36  tff(c_146822, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_144477, c_146815])).
% 28.79/18.36  tff(c_146923, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_146822])).
% 28.79/18.36  tff(c_146926, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_103894, c_146923])).
% 28.79/18.36  tff(c_146930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_146926])).
% 28.79/18.36  tff(c_146931, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_146822])).
% 28.79/18.36  tff(c_147732, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_147729, c_146931])).
% 28.79/18.36  tff(c_147745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_82927, c_147732])).
% 28.79/18.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.79/18.36  
% 28.79/18.36  Inference rules
% 28.79/18.36  ----------------------
% 28.79/18.36  #Ref     : 0
% 28.79/18.36  #Sup     : 36484
% 28.79/18.36  #Fact    : 0
% 28.79/18.36  #Define  : 0
% 28.79/18.36  #Split   : 320
% 28.79/18.36  #Chain   : 0
% 28.79/18.36  #Close   : 0
% 28.79/18.36  
% 28.79/18.36  Ordering : KBO
% 28.79/18.36  
% 28.79/18.36  Simplification rules
% 28.79/18.36  ----------------------
% 28.79/18.36  #Subsume      : 12368
% 28.79/18.36  #Demod        : 56863
% 28.79/18.36  #Tautology    : 14065
% 28.79/18.36  #SimpNegUnit  : 306
% 28.79/18.36  #BackRed      : 2490
% 28.79/18.36  
% 28.79/18.36  #Partial instantiations: 3306
% 28.79/18.36  #Strategies tried      : 1
% 28.79/18.36  
% 28.79/18.36  Timing (in seconds)
% 28.79/18.36  ----------------------
% 28.79/18.36  Preprocessing        : 0.40
% 28.79/18.36  Parsing              : 0.22
% 28.79/18.36  CNF conversion       : 0.03
% 28.79/18.36  Main loop            : 16.93
% 28.79/18.36  Inferencing          : 3.76
% 28.79/18.36  Reduction            : 6.71
% 28.79/18.36  Demodulation         : 5.20
% 28.79/18.36  BG Simplification    : 0.33
% 28.79/18.36  Subsumption          : 5.33
% 28.79/18.36  Abstraction          : 0.51
% 28.79/18.36  MUC search           : 0.00
% 28.79/18.36  Cooper               : 0.00
% 28.79/18.36  Total                : 17.55
% 28.79/18.36  Index Insertion      : 0.00
% 28.79/18.36  Index Deletion       : 0.00
% 28.79/18.36  Index Matching       : 0.00
% 28.79/18.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
