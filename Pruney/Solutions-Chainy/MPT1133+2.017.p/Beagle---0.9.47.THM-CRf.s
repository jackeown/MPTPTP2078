%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:14 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 10.45s
% Verified   : 
% Statistics : Number of formulae       :  543 (11927 expanded)
%              Number of leaves         :   51 (3801 expanded)
%              Depth                    :   28
%              Number of atoms          : 1784 (48734 expanded)
%              Number of equality atoms :   59 (6237 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_mcart_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_230,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_134,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_130,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_142,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_200,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_171,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_84,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_9246,plain,(
    ! [A_1314] :
      ( m1_subset_1(u1_pre_topc(A_1314),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1314))))
      | ~ l1_pre_topc(A_1314) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ! [A_48,B_49] :
      ( l1_pre_topc(g1_pre_topc(A_48,B_49))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_9253,plain,(
    ! [A_1314] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_1314),u1_pre_topc(A_1314)))
      | ~ l1_pre_topc(A_1314) ) ),
    inference(resolution,[status(thm)],[c_9246,c_48])).

tff(c_86,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_54,plain,(
    ! [A_51] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_51),u1_pre_topc(A_51)))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_76,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_34,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_163,plain,(
    ! [C_105,B_106,A_107] :
      ( v5_relat_1(C_105,B_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_177,plain,(
    v5_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_163])).

tff(c_66,plain,(
    '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_99,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68])).

tff(c_28,plain,(
    ! [C_19,A_17,B_18] :
      ( v4_relat_1(C_19,A_17)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_253,plain,(
    v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_99,c_28])).

tff(c_70,plain,(
    v1_funct_2('#skF_5',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_98,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70])).

tff(c_2442,plain,(
    ! [B_502,C_503,A_504] :
      ( k1_xboole_0 = B_502
      | v1_partfun1(C_503,A_504)
      | ~ v1_funct_2(C_503,A_504,B_502)
      | ~ m1_subset_1(C_503,k1_zfmisc_1(k2_zfmisc_1(A_504,B_502)))
      | ~ v1_funct_1(C_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2451,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_2442])).

tff(c_2473,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_98,c_2451])).

tff(c_2769,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2473])).

tff(c_24,plain,(
    ! [C_16,A_14,B_15] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_24])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(B_11),A_10)
      | ~ v4_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2296,plain,(
    ! [D_489,C_490,B_491,A_492] :
      ( m1_subset_1(D_489,k1_zfmisc_1(k2_zfmisc_1(C_490,B_491)))
      | ~ r1_tarski(k2_relat_1(D_489),B_491)
      | ~ m1_subset_1(D_489,k1_zfmisc_1(k2_zfmisc_1(C_490,A_492))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2309,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),B_491)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_491) ) ),
    inference(resolution,[status(thm)],[c_74,c_2296])).

tff(c_2356,plain,(
    ! [D_495,B_496,C_497,A_498] :
      ( m1_subset_1(D_495,k1_zfmisc_1(k2_zfmisc_1(B_496,C_497)))
      | ~ r1_tarski(k1_relat_1(D_495),B_496)
      | ~ m1_subset_1(D_495,k1_zfmisc_1(k2_zfmisc_1(A_498,C_497))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2618,plain,(
    ! [B_521,B_522] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_521,B_522)))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_521)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_522) ) ),
    inference(resolution,[status(thm)],[c_2309,c_2356])).

tff(c_40,plain,(
    ! [C_44,A_42,B_43] :
      ( v1_funct_2(C_44,A_42,B_43)
      | ~ v1_partfun1(C_44,A_42)
      | ~ v1_funct_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2632,plain,(
    ! [B_521,B_522] :
      ( v1_funct_2('#skF_4',B_521,B_522)
      | ~ v1_partfun1('#skF_4',B_521)
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_521)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_522) ) ),
    inference(resolution,[status(thm)],[c_2618,c_40])).

tff(c_3000,plain,(
    ! [B_560,B_561] :
      ( v1_funct_2('#skF_4',B_560,B_561)
      | ~ v1_partfun1('#skF_4',B_560)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_560)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_561) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2632])).

tff(c_3003,plain,(
    ! [A_10,B_561] :
      ( v1_funct_2('#skF_4',A_10,B_561)
      | ~ v1_partfun1('#skF_4',A_10)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_561)
      | ~ v4_relat_1('#skF_4',A_10)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_3000])).

tff(c_3059,plain,(
    ! [A_565,B_566] :
      ( v1_funct_2('#skF_4',A_565,B_566)
      | ~ v1_partfun1('#skF_4',A_565)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_566)
      | ~ v4_relat_1('#skF_4',A_565) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3003])).

tff(c_3062,plain,(
    ! [A_565,A_12] :
      ( v1_funct_2('#skF_4',A_565,A_12)
      | ~ v1_partfun1('#skF_4',A_565)
      | ~ v4_relat_1('#skF_4',A_565)
      | ~ v5_relat_1('#skF_4',A_12)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_3059])).

tff(c_3065,plain,(
    ! [A_565,A_12] :
      ( v1_funct_2('#skF_4',A_565,A_12)
      | ~ v1_partfun1('#skF_4',A_565)
      | ~ v4_relat_1('#skF_4',A_565)
      | ~ v5_relat_1('#skF_4',A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_3062])).

tff(c_2308,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),B_491)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_491) ) ),
    inference(resolution,[status(thm)],[c_99,c_2296])).

tff(c_210,plain,(
    ! [A_120] :
      ( m1_subset_1(u1_pre_topc(A_120),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120))))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_217,plain,(
    ! [A_120] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_120),u1_pre_topc(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_210,c_48])).

tff(c_789,plain,(
    ! [B_224,C_225,A_226] :
      ( k1_xboole_0 = B_224
      | v1_partfun1(C_225,A_226)
      | ~ v1_funct_2(C_225,A_226,B_224)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_226,B_224)))
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_804,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_789])).

tff(c_830,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_xboole_0
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_98,c_804])).

tff(c_924,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_830])).

tff(c_375,plain,(
    ! [D_180,C_181,B_182,A_183] :
      ( m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(C_181,B_182)))
      | ~ r1_tarski(k2_relat_1(D_180),B_182)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(C_181,A_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_387,plain,(
    ! [B_182] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),B_182)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_182) ) ),
    inference(resolution,[status(thm)],[c_99,c_375])).

tff(c_82,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_88,plain,
    ( ~ v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_96,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_88])).

tff(c_287,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_94,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_5',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_95,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_94])).

tff(c_313,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_95])).

tff(c_1300,plain,(
    ! [D_283,A_284,B_285] :
      ( v5_pre_topc(D_283,A_284,B_285)
      | ~ v5_pre_topc(D_283,A_284,g1_pre_topc(u1_struct_0(B_285),u1_pre_topc(B_285)))
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_284),u1_struct_0(g1_pre_topc(u1_struct_0(B_285),u1_pre_topc(B_285))))))
      | ~ v1_funct_2(D_283,u1_struct_0(A_284),u1_struct_0(g1_pre_topc(u1_struct_0(B_285),u1_pre_topc(B_285))))
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_284),u1_struct_0(B_285))))
      | ~ v1_funct_2(D_283,u1_struct_0(A_284),u1_struct_0(B_285))
      | ~ v1_funct_1(D_283)
      | ~ l1_pre_topc(B_285)
      | ~ v2_pre_topc(B_285)
      | ~ l1_pre_topc(A_284)
      | ~ v2_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1327,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_99,c_1300])).

tff(c_1348,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_98,c_313,c_1327])).

tff(c_1365,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1348])).

tff(c_1368,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1365])).

tff(c_1372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_1368])).

tff(c_1373,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1348])).

tff(c_1414,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1373])).

tff(c_1434,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_387,c_1414])).

tff(c_1437,plain,
    ( ~ v5_relat_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1434])).

tff(c_1441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_177,c_1437])).

tff(c_1443,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_1373])).

tff(c_1459,plain,
    ( v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1443,c_40])).

tff(c_1488,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_924,c_1459])).

tff(c_58,plain,(
    ! [D_66,A_52,B_60] :
      ( v5_pre_topc(D_66,A_52,B_60)
      | ~ v5_pre_topc(D_66,g1_pre_topc(u1_struct_0(A_52),u1_pre_topc(A_52)),B_60)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_52),u1_pre_topc(A_52))),u1_struct_0(B_60))))
      | ~ v1_funct_2(D_66,u1_struct_0(g1_pre_topc(u1_struct_0(A_52),u1_pre_topc(A_52))),u1_struct_0(B_60))
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_52),u1_struct_0(B_60))))
      | ~ v1_funct_2(D_66,u1_struct_0(A_52),u1_struct_0(B_60))
      | ~ v1_funct_1(D_66)
      | ~ l1_pre_topc(B_60)
      | ~ v2_pre_topc(B_60)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1446,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1443,c_58])).

tff(c_1475,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_1446])).

tff(c_1476,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_1475])).

tff(c_1497,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1476])).

tff(c_1509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1497])).

tff(c_1510,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1476])).

tff(c_1442,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1373])).

tff(c_1524,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_1442])).

tff(c_1525,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_1524])).

tff(c_1528,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_217,c_1525])).

tff(c_1532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1528])).

tff(c_1533,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_830])).

tff(c_14,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_254,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ r2_hidden(A_7,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_99,c_14])).

tff(c_363,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_1535,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1533,c_363])).

tff(c_1541,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6,c_1535])).

tff(c_1544,plain,(
    ! [A_302] : ~ r2_hidden(A_302,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_1549,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_1544])).

tff(c_1572,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_2])).

tff(c_1571,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_1549,c_6])).

tff(c_10,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1569,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_10])).

tff(c_46,plain,(
    ! [B_46,C_47,A_45] :
      ( k1_xboole_0 = B_46
      | v1_partfun1(C_47,A_45)
      | ~ v1_funct_2(C_47,A_45,B_46)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46)))
      | ~ v1_funct_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1731,plain,(
    ! [B_324,C_325,A_326] :
      ( B_324 = '#skF_4'
      | v1_partfun1(C_325,A_326)
      | ~ v1_funct_2(C_325,A_326,B_324)
      | ~ m1_subset_1(C_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_324)))
      | ~ v1_funct_1(C_325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_46])).

tff(c_1741,plain,(
    ! [B_324,A_326] :
      ( B_324 = '#skF_4'
      | v1_partfun1('#skF_4',A_326)
      | ~ v1_funct_2('#skF_4',A_326,B_324)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1569,c_1731])).

tff(c_1778,plain,(
    ! [B_343,A_344] :
      ( B_343 = '#skF_4'
      | v1_partfun1('#skF_4',A_344)
      | ~ v1_funct_2('#skF_4',A_344,B_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1741])).

tff(c_1790,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_1778])).

tff(c_1791,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1790])).

tff(c_1587,plain,(
    ! [A_306] : m1_subset_1('#skF_4',k1_zfmisc_1(A_306)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1549,c_10])).

tff(c_1591,plain,(
    ! [A_42,B_43] :
      ( v1_funct_2('#skF_4',A_42,B_43)
      | ~ v1_partfun1('#skF_4',A_42)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1587,c_40])).

tff(c_1618,plain,(
    ! [A_42,B_43] :
      ( v1_funct_2('#skF_4',A_42,B_43)
      | ~ v1_partfun1('#skF_4',A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1591])).

tff(c_1800,plain,(
    ! [D_353,A_354,B_355] :
      ( v5_pre_topc(D_353,A_354,B_355)
      | ~ v5_pre_topc(D_353,g1_pre_topc(u1_struct_0(A_354),u1_pre_topc(A_354)),B_355)
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_354),u1_pre_topc(A_354))),u1_struct_0(B_355))))
      | ~ v1_funct_2(D_353,u1_struct_0(g1_pre_topc(u1_struct_0(A_354),u1_pre_topc(A_354))),u1_struct_0(B_355))
      | ~ m1_subset_1(D_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_354),u1_struct_0(B_355))))
      | ~ v1_funct_2(D_353,u1_struct_0(A_354),u1_struct_0(B_355))
      | ~ v1_funct_1(D_353)
      | ~ l1_pre_topc(B_355)
      | ~ v2_pre_topc(B_355)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1804,plain,(
    ! [A_354,B_355] :
      ( v5_pre_topc('#skF_4',A_354,B_355)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_354),u1_pre_topc(A_354)),B_355)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_354),u1_pre_topc(A_354))),u1_struct_0(B_355))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_354),u1_struct_0(B_355))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_354),u1_struct_0(B_355))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_355)
      | ~ v2_pre_topc(B_355)
      | ~ l1_pre_topc(A_354)
      | ~ v2_pre_topc(A_354) ) ),
    inference(resolution,[status(thm)],[c_1569,c_1800])).

tff(c_2046,plain,(
    ! [A_402,B_403] :
      ( v5_pre_topc('#skF_4',A_402,B_403)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_402),u1_pre_topc(A_402)),B_403)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_402),u1_pre_topc(A_402))),u1_struct_0(B_403))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_402),u1_struct_0(B_403))
      | ~ l1_pre_topc(B_403)
      | ~ v2_pre_topc(B_403)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1569,c_1804])).

tff(c_2052,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_2046])).

tff(c_2056,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_313,c_2052])).

tff(c_2065,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2056])).

tff(c_2068,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_2065])).

tff(c_2072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2068])).

tff(c_2073,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2056])).

tff(c_2108,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_2073])).

tff(c_2111,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1618,c_2108])).

tff(c_2115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_2111])).

tff(c_2116,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2073])).

tff(c_2129,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2116])).

tff(c_2132,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_217,c_2129])).

tff(c_2136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2132])).

tff(c_2137,plain,(
    v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2116])).

tff(c_2117,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_2073])).

tff(c_1839,plain,(
    ! [D_365,A_366,B_367] :
      ( v5_pre_topc(D_365,A_366,B_367)
      | ~ v5_pre_topc(D_365,A_366,g1_pre_topc(u1_struct_0(B_367),u1_pre_topc(B_367)))
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366),u1_struct_0(g1_pre_topc(u1_struct_0(B_367),u1_pre_topc(B_367))))))
      | ~ v1_funct_2(D_365,u1_struct_0(A_366),u1_struct_0(g1_pre_topc(u1_struct_0(B_367),u1_pre_topc(B_367))))
      | ~ m1_subset_1(D_365,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366),u1_struct_0(B_367))))
      | ~ v1_funct_2(D_365,u1_struct_0(A_366),u1_struct_0(B_367))
      | ~ v1_funct_1(D_365)
      | ~ l1_pre_topc(B_367)
      | ~ v2_pre_topc(B_367)
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1843,plain,(
    ! [A_366,B_367] :
      ( v5_pre_topc('#skF_4',A_366,B_367)
      | ~ v5_pre_topc('#skF_4',A_366,g1_pre_topc(u1_struct_0(B_367),u1_pre_topc(B_367)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_366),u1_struct_0(g1_pre_topc(u1_struct_0(B_367),u1_pre_topc(B_367))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366),u1_struct_0(B_367))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_366),u1_struct_0(B_367))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_367)
      | ~ v2_pre_topc(B_367)
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366) ) ),
    inference(resolution,[status(thm)],[c_1569,c_1839])).

tff(c_2139,plain,(
    ! [A_420,B_421] :
      ( v5_pre_topc('#skF_4',A_420,B_421)
      | ~ v5_pre_topc('#skF_4',A_420,g1_pre_topc(u1_struct_0(B_421),u1_pre_topc(B_421)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_420),u1_struct_0(g1_pre_topc(u1_struct_0(B_421),u1_pre_topc(B_421))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_420),u1_struct_0(B_421))
      | ~ l1_pre_topc(B_421)
      | ~ v2_pre_topc(B_421)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1569,c_1843])).

tff(c_2142,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2117,c_2139])).

tff(c_2151,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_76,c_2142])).

tff(c_2152,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_287,c_2151])).

tff(c_2158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2152])).

tff(c_2159,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1790])).

tff(c_193,plain,(
    ! [C_114,B_115,A_116] :
      ( ~ v1_xboole_0(C_114)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(C_114))
      | ~ r2_hidden(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [A_116] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_116,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_74,c_193])).

tff(c_200,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_2163,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2159,c_200])).

tff(c_2168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_1571,c_2163])).

tff(c_2169,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_2547,plain,(
    ! [D_515,A_516,B_517] :
      ( v5_pre_topc(D_515,A_516,g1_pre_topc(u1_struct_0(B_517),u1_pre_topc(B_517)))
      | ~ v5_pre_topc(D_515,A_516,B_517)
      | ~ m1_subset_1(D_515,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_516),u1_struct_0(g1_pre_topc(u1_struct_0(B_517),u1_pre_topc(B_517))))))
      | ~ v1_funct_2(D_515,u1_struct_0(A_516),u1_struct_0(g1_pre_topc(u1_struct_0(B_517),u1_pre_topc(B_517))))
      | ~ m1_subset_1(D_515,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_516),u1_struct_0(B_517))))
      | ~ v1_funct_2(D_515,u1_struct_0(A_516),u1_struct_0(B_517))
      | ~ v1_funct_1(D_515)
      | ~ l1_pre_topc(B_517)
      | ~ v2_pre_topc(B_517)
      | ~ l1_pre_topc(A_516)
      | ~ v2_pre_topc(A_516) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2558,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_99,c_2547])).

tff(c_2569,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_98,c_2558])).

tff(c_2570,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2169,c_2569])).

tff(c_3103,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2570])).

tff(c_3106,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_3103])).

tff(c_3110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_3106])).

tff(c_3111,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2570])).

tff(c_3152,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3111])).

tff(c_2170,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_2719,plain,(
    ! [B_524] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),B_524)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_524) ) ),
    inference(resolution,[status(thm)],[c_99,c_2296])).

tff(c_2733,plain,(
    ! [B_524] :
      ( v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),B_524)
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v1_funct_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_524) ) ),
    inference(resolution,[status(thm)],[c_2719,c_40])).

tff(c_2761,plain,(
    ! [B_524] :
      ( v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),B_524)
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_2733])).

tff(c_3460,plain,(
    ! [B_611] :
      ( v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),B_611)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2769,c_2761])).

tff(c_2372,plain,(
    ! [B_496] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_496,u1_struct_0('#skF_3'))))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_496) ) ),
    inference(resolution,[status(thm)],[c_74,c_2356])).

tff(c_2783,plain,(
    ! [D_531,A_532,B_533] :
      ( v5_pre_topc(D_531,g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532)),B_533)
      | ~ v5_pre_topc(D_531,A_532,B_533)
      | ~ m1_subset_1(D_531,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532))),u1_struct_0(B_533))))
      | ~ v1_funct_2(D_531,u1_struct_0(g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532))),u1_struct_0(B_533))
      | ~ m1_subset_1(D_531,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532),u1_struct_0(B_533))))
      | ~ v1_funct_2(D_531,u1_struct_0(A_532),u1_struct_0(B_533))
      | ~ v1_funct_1(D_531)
      | ~ l1_pre_topc(B_533)
      | ~ v2_pre_topc(B_533)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_2807,plain,(
    ! [A_532] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_532,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532))),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_532),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532)))) ) ),
    inference(resolution,[status(thm)],[c_2372,c_2783])).

tff(c_2828,plain,(
    ! [A_532] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_532,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532))),u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_532),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(A_532),u1_pre_topc(A_532)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_2807])).

tff(c_3464,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ r1_tarski(k2_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3460,c_2828])).

tff(c_3477,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ r1_tarski(k2_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_76,c_74,c_2170,c_3464])).

tff(c_3478,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ r1_tarski(k2_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_3152,c_3477])).

tff(c_3489,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3478])).

tff(c_3492,plain,
    ( ~ v5_relat_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3489])).

tff(c_3496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_177,c_3492])).

tff(c_3497,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_3478])).

tff(c_3556,plain,
    ( ~ v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_3497])).

tff(c_3560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_253,c_3556])).

tff(c_3561,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_3111])).

tff(c_3595,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3561])).

tff(c_3598,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_217,c_3595])).

tff(c_3602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_3598])).

tff(c_3603,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_3561])).

tff(c_3711,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_3603])).

tff(c_3727,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2308,c_3711])).

tff(c_3734,plain,
    ( ~ v5_relat_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3727])).

tff(c_3738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_177,c_3734])).

tff(c_3739,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3603])).

tff(c_3746,plain,
    ( ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v4_relat_1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
    | ~ v5_relat_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3065,c_3739])).

tff(c_3754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_253,c_2769,c_3746])).

tff(c_3755,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2473])).

tff(c_2252,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_3786,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3755,c_2252])).

tff(c_3794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6,c_3786])).

tff(c_3797,plain,(
    ! [A_628] : ~ r2_hidden(A_628,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_3802,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_3797])).

tff(c_3822,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3802,c_2])).

tff(c_3821,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3802,c_3802,c_6])).

tff(c_3819,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3802,c_10])).

tff(c_4001,plain,(
    ! [B_665,C_666,A_667] :
      ( B_665 = '#skF_4'
      | v1_partfun1(C_666,A_667)
      | ~ v1_funct_2(C_666,A_667,B_665)
      | ~ m1_subset_1(C_666,k1_zfmisc_1(k2_zfmisc_1(A_667,B_665)))
      | ~ v1_funct_1(C_666) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3802,c_46])).

tff(c_4008,plain,(
    ! [B_665,A_667] :
      ( B_665 = '#skF_4'
      | v1_partfun1('#skF_4',A_667)
      | ~ v1_funct_2('#skF_4',A_667,B_665)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3819,c_4001])).

tff(c_4016,plain,(
    ! [B_668,A_669] :
      ( B_668 = '#skF_4'
      | v1_partfun1('#skF_4',A_669)
      | ~ v1_funct_2('#skF_4',A_669,B_668) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4008])).

tff(c_4028,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_4016])).

tff(c_4029,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4028])).

tff(c_3913,plain,(
    ! [C_638,A_639,B_640] :
      ( v1_funct_2(C_638,A_639,B_640)
      | ~ v1_partfun1(C_638,A_639)
      | ~ v1_funct_1(C_638)
      | ~ m1_subset_1(C_638,k1_zfmisc_1(k2_zfmisc_1(A_639,B_640))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3920,plain,(
    ! [A_639,B_640] :
      ( v1_funct_2('#skF_4',A_639,B_640)
      | ~ v1_partfun1('#skF_4',A_639)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3819,c_3913])).

tff(c_3926,plain,(
    ! [A_639,B_640] :
      ( v1_funct_2('#skF_4',A_639,B_640)
      | ~ v1_partfun1('#skF_4',A_639) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3920])).

tff(c_4045,plain,(
    ! [D_680,A_681,B_682] :
      ( v5_pre_topc(D_680,A_681,g1_pre_topc(u1_struct_0(B_682),u1_pre_topc(B_682)))
      | ~ v5_pre_topc(D_680,A_681,B_682)
      | ~ m1_subset_1(D_680,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_681),u1_struct_0(g1_pre_topc(u1_struct_0(B_682),u1_pre_topc(B_682))))))
      | ~ v1_funct_2(D_680,u1_struct_0(A_681),u1_struct_0(g1_pre_topc(u1_struct_0(B_682),u1_pre_topc(B_682))))
      | ~ m1_subset_1(D_680,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_681),u1_struct_0(B_682))))
      | ~ v1_funct_2(D_680,u1_struct_0(A_681),u1_struct_0(B_682))
      | ~ v1_funct_1(D_680)
      | ~ l1_pre_topc(B_682)
      | ~ v2_pre_topc(B_682)
      | ~ l1_pre_topc(A_681)
      | ~ v2_pre_topc(A_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_4049,plain,(
    ! [A_681,B_682] :
      ( v5_pre_topc('#skF_4',A_681,g1_pre_topc(u1_struct_0(B_682),u1_pre_topc(B_682)))
      | ~ v5_pre_topc('#skF_4',A_681,B_682)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_681),u1_struct_0(g1_pre_topc(u1_struct_0(B_682),u1_pre_topc(B_682))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_681),u1_struct_0(B_682))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_681),u1_struct_0(B_682))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_682)
      | ~ v2_pre_topc(B_682)
      | ~ l1_pre_topc(A_681)
      | ~ v2_pre_topc(A_681) ) ),
    inference(resolution,[status(thm)],[c_3819,c_4045])).

tff(c_4378,plain,(
    ! [A_761,B_762] :
      ( v5_pre_topc('#skF_4',A_761,g1_pre_topc(u1_struct_0(B_762),u1_pre_topc(B_762)))
      | ~ v5_pre_topc('#skF_4',A_761,B_762)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_761),u1_struct_0(g1_pre_topc(u1_struct_0(B_762),u1_pre_topc(B_762))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_761),u1_struct_0(B_762))
      | ~ l1_pre_topc(B_762)
      | ~ v2_pre_topc(B_762)
      | ~ l1_pre_topc(A_761)
      | ~ v2_pre_topc(A_761) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3819,c_4049])).

tff(c_4385,plain,(
    ! [A_761,B_762] :
      ( v5_pre_topc('#skF_4',A_761,g1_pre_topc(u1_struct_0(B_762),u1_pre_topc(B_762)))
      | ~ v5_pre_topc('#skF_4',A_761,B_762)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_761),u1_struct_0(B_762))
      | ~ l1_pre_topc(B_762)
      | ~ v2_pre_topc(B_762)
      | ~ l1_pre_topc(A_761)
      | ~ v2_pre_topc(A_761)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_761)) ) ),
    inference(resolution,[status(thm)],[c_3926,c_4378])).

tff(c_4180,plain,(
    ! [D_702,A_703,B_704] :
      ( v5_pre_topc(D_702,g1_pre_topc(u1_struct_0(A_703),u1_pre_topc(A_703)),B_704)
      | ~ v5_pre_topc(D_702,A_703,B_704)
      | ~ m1_subset_1(D_702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_703),u1_pre_topc(A_703))),u1_struct_0(B_704))))
      | ~ v1_funct_2(D_702,u1_struct_0(g1_pre_topc(u1_struct_0(A_703),u1_pre_topc(A_703))),u1_struct_0(B_704))
      | ~ m1_subset_1(D_702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703),u1_struct_0(B_704))))
      | ~ v1_funct_2(D_702,u1_struct_0(A_703),u1_struct_0(B_704))
      | ~ v1_funct_1(D_702)
      | ~ l1_pre_topc(B_704)
      | ~ v2_pre_topc(B_704)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_4192,plain,(
    ! [A_703,B_704] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_703),u1_pre_topc(A_703)),B_704)
      | ~ v5_pre_topc('#skF_4',A_703,B_704)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_703),u1_pre_topc(A_703))),u1_struct_0(B_704))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703),u1_struct_0(B_704))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_703),u1_struct_0(B_704))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_704)
      | ~ v2_pre_topc(B_704)
      | ~ l1_pre_topc(A_703)
      | ~ v2_pre_topc(A_703) ) ),
    inference(resolution,[status(thm)],[c_3819,c_4180])).

tff(c_4401,plain,(
    ! [A_765,B_766] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_765),u1_pre_topc(A_765)),B_766)
      | ~ v5_pre_topc('#skF_4',A_765,B_766)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_765),u1_pre_topc(A_765))),u1_struct_0(B_766))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_765),u1_struct_0(B_766))
      | ~ l1_pre_topc(B_766)
      | ~ v2_pre_topc(B_766)
      | ~ l1_pre_topc(A_765)
      | ~ v2_pre_topc(A_765) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3819,c_4192])).

tff(c_4407,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_4401])).

tff(c_4411,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4407])).

tff(c_4412,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_2169,c_4411])).

tff(c_4423,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4412])).

tff(c_4426,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_4423])).

tff(c_4430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_4426])).

tff(c_4431,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4412])).

tff(c_4434,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4431])).

tff(c_4448,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4385,c_4434])).

tff(c_4452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4029,c_86,c_84,c_82,c_80,c_76,c_2170,c_4448])).

tff(c_4453,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4431])).

tff(c_4461,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4453])).

tff(c_4467,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_217,c_4461])).

tff(c_4471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4467])).

tff(c_4472,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_4453])).

tff(c_4476,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3926,c_4472])).

tff(c_4480,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4029,c_4476])).

tff(c_4481,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4028])).

tff(c_4485,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4481,c_200])).

tff(c_4490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3822,c_3821,c_4485])).

tff(c_4493,plain,(
    ! [A_769] : ~ r2_hidden(A_769,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_4498,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_4493])).

tff(c_4507,plain,(
    ! [A_3] : m1_subset_1('#skF_4',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_10])).

tff(c_9533,plain,(
    ! [B_1409,C_1410,A_1411] :
      ( B_1409 = '#skF_4'
      | v1_partfun1(C_1410,A_1411)
      | ~ v1_funct_2(C_1410,A_1411,B_1409)
      | ~ m1_subset_1(C_1410,k1_zfmisc_1(k2_zfmisc_1(A_1411,B_1409)))
      | ~ v1_funct_1(C_1410) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_46])).

tff(c_9543,plain,(
    ! [B_1409,A_1411] :
      ( B_1409 = '#skF_4'
      | v1_partfun1('#skF_4',A_1411)
      | ~ v1_funct_2('#skF_4',A_1411,B_1409)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4507,c_9533])).

tff(c_9556,plain,(
    ! [B_1412,A_1413] :
      ( B_1412 = '#skF_4'
      | v1_partfun1('#skF_4',A_1413)
      | ~ v1_funct_2('#skF_4',A_1413,B_1412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9543])).

tff(c_9568,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_9556])).

tff(c_9569,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9568])).

tff(c_4518,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_4854,plain,(
    ! [B_866,C_867,A_868] :
      ( B_866 = '#skF_4'
      | v1_partfun1(C_867,A_868)
      | ~ v1_funct_2(C_867,A_868,B_866)
      | ~ m1_subset_1(C_867,k1_zfmisc_1(k2_zfmisc_1(A_868,B_866)))
      | ~ v1_funct_1(C_867) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_46])).

tff(c_4867,plain,(
    ! [B_866,A_868] :
      ( B_866 = '#skF_4'
      | v1_partfun1('#skF_4',A_868)
      | ~ v1_funct_2('#skF_4',A_868,B_866)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4507,c_4854])).

tff(c_4877,plain,(
    ! [B_869,A_870] :
      ( B_869 = '#skF_4'
      | v1_partfun1('#skF_4',A_870)
      | ~ v1_funct_2('#skF_4',A_870,B_869) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4867])).

tff(c_4889,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_4877])).

tff(c_4890,plain,(
    v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4889])).

tff(c_4691,plain,(
    ! [C_824,A_825,B_826] :
      ( v1_funct_2(C_824,A_825,B_826)
      | ~ v1_partfun1(C_824,A_825)
      | ~ v1_funct_1(C_824)
      | ~ m1_subset_1(C_824,k1_zfmisc_1(k2_zfmisc_1(A_825,B_826))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4698,plain,(
    ! [A_825,B_826] :
      ( v1_funct_2('#skF_4',A_825,B_826)
      | ~ v1_partfun1('#skF_4',A_825)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4507,c_4691])).

tff(c_4704,plain,(
    ! [A_825,B_826] :
      ( v1_funct_2('#skF_4',A_825,B_826)
      | ~ v1_partfun1('#skF_4',A_825) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4698])).

tff(c_4574,plain,(
    ! [A_777] :
      ( m1_subset_1(u1_pre_topc(A_777),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_777))))
      | ~ l1_pre_topc(A_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4581,plain,(
    ! [A_777] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_777),u1_pre_topc(A_777)))
      | ~ l1_pre_topc(A_777) ) ),
    inference(resolution,[status(thm)],[c_4574,c_48])).

tff(c_4888,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_98,c_4877])).

tff(c_4891,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_4888])).

tff(c_4584,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_4518,c_95])).

tff(c_4999,plain,(
    ! [D_903,A_904,B_905] :
      ( v5_pre_topc(D_903,A_904,B_905)
      | ~ v5_pre_topc(D_903,A_904,g1_pre_topc(u1_struct_0(B_905),u1_pre_topc(B_905)))
      | ~ m1_subset_1(D_903,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904),u1_struct_0(g1_pre_topc(u1_struct_0(B_905),u1_pre_topc(B_905))))))
      | ~ v1_funct_2(D_903,u1_struct_0(A_904),u1_struct_0(g1_pre_topc(u1_struct_0(B_905),u1_pre_topc(B_905))))
      | ~ m1_subset_1(D_903,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904),u1_struct_0(B_905))))
      | ~ v1_funct_2(D_903,u1_struct_0(A_904),u1_struct_0(B_905))
      | ~ v1_funct_1(D_903)
      | ~ l1_pre_topc(B_905)
      | ~ v2_pre_topc(B_905)
      | ~ l1_pre_topc(A_904)
      | ~ v2_pre_topc(A_904) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_5011,plain,(
    ! [A_904,B_905] :
      ( v5_pre_topc('#skF_4',A_904,B_905)
      | ~ v5_pre_topc('#skF_4',A_904,g1_pre_topc(u1_struct_0(B_905),u1_pre_topc(B_905)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_904),u1_struct_0(g1_pre_topc(u1_struct_0(B_905),u1_pre_topc(B_905))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904),u1_struct_0(B_905))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_904),u1_struct_0(B_905))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_905)
      | ~ v2_pre_topc(B_905)
      | ~ l1_pre_topc(A_904)
      | ~ v2_pre_topc(A_904) ) ),
    inference(resolution,[status(thm)],[c_4507,c_4999])).

tff(c_5118,plain,(
    ! [A_930,B_931] :
      ( v5_pre_topc('#skF_4',A_930,B_931)
      | ~ v5_pre_topc('#skF_4',A_930,g1_pre_topc(u1_struct_0(B_931),u1_pre_topc(B_931)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_930),u1_struct_0(g1_pre_topc(u1_struct_0(B_931),u1_pre_topc(B_931))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_930),u1_struct_0(B_931))
      | ~ l1_pre_topc(B_931)
      | ~ v2_pre_topc(B_931)
      | ~ l1_pre_topc(A_930)
      | ~ v2_pre_topc(A_930) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_5011])).

tff(c_5124,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_98,c_5118])).

tff(c_5128,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_4584,c_5124])).

tff(c_5147,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5128])).

tff(c_5150,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_5147])).

tff(c_5154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_5150])).

tff(c_5155,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5128])).

tff(c_5168,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5155])).

tff(c_5171,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_4704,c_5168])).

tff(c_5175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4891,c_5171])).

tff(c_5177,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5155])).

tff(c_5073,plain,(
    ! [D_919,A_920,B_921] :
      ( v5_pre_topc(D_919,A_920,B_921)
      | ~ v5_pre_topc(D_919,g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920)),B_921)
      | ~ m1_subset_1(D_919,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920))),u1_struct_0(B_921))))
      | ~ v1_funct_2(D_919,u1_struct_0(g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920))),u1_struct_0(B_921))
      | ~ m1_subset_1(D_919,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_920),u1_struct_0(B_921))))
      | ~ v1_funct_2(D_919,u1_struct_0(A_920),u1_struct_0(B_921))
      | ~ v1_funct_1(D_919)
      | ~ l1_pre_topc(B_921)
      | ~ v2_pre_topc(B_921)
      | ~ l1_pre_topc(A_920)
      | ~ v2_pre_topc(A_920) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_5085,plain,(
    ! [A_920,B_921] :
      ( v5_pre_topc('#skF_4',A_920,B_921)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920)),B_921)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920))),u1_struct_0(B_921))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_920),u1_struct_0(B_921))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_920),u1_struct_0(B_921))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_921)
      | ~ v2_pre_topc(B_921)
      | ~ l1_pre_topc(A_920)
      | ~ v2_pre_topc(A_920) ) ),
    inference(resolution,[status(thm)],[c_4507,c_5073])).

tff(c_5090,plain,(
    ! [A_920,B_921] :
      ( v5_pre_topc('#skF_4',A_920,B_921)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920)),B_921)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_920),u1_pre_topc(A_920))),u1_struct_0(B_921))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_920),u1_struct_0(B_921))
      | ~ l1_pre_topc(B_921)
      | ~ v2_pre_topc(B_921)
      | ~ l1_pre_topc(A_920)
      | ~ v2_pre_topc(A_920) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_5085])).

tff(c_5180,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_5177,c_5090])).

tff(c_5196,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_76,c_5180])).

tff(c_5197,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_4518,c_5196])).

tff(c_5176,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5155])).

tff(c_5219,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_5197,c_5176])).

tff(c_5222,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4581,c_5219])).

tff(c_5226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5222])).

tff(c_5227,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4888])).

tff(c_5250,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5227,c_4581])).

tff(c_5305,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5250])).

tff(c_5308,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_4581,c_5305])).

tff(c_5312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5308])).

tff(c_5314,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5250])).

tff(c_4506,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | A_28 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_34])).

tff(c_52,plain,(
    ! [A_50] :
      ( m1_subset_1(u1_pre_topc(A_50),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50))))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_5253,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5227,c_52])).

tff(c_5432,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5314,c_5253])).

tff(c_12,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5452,plain,(
    ! [A_962] :
      ( m1_subset_1(A_962,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_962,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ) ),
    inference(resolution,[status(thm)],[c_5432,c_12])).

tff(c_5457,plain,
    ( m1_subset_1('#skF_1'(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),k1_zfmisc_1('#skF_4'))
    | u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4506,c_5452])).

tff(c_5466,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5457])).

tff(c_5489,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_4'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5466,c_54])).

tff(c_5510,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4','#skF_4'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5314,c_5227,c_5489])).

tff(c_5556,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_5510])).

tff(c_5559,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_5556])).

tff(c_5563,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_5559])).

tff(c_5565,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_5510])).

tff(c_5266,plain,(
    ! [D_936,A_937,B_938] :
      ( v5_pre_topc(D_936,A_937,B_938)
      | ~ v5_pre_topc(D_936,A_937,g1_pre_topc(u1_struct_0(B_938),u1_pre_topc(B_938)))
      | ~ m1_subset_1(D_936,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_937),u1_struct_0(g1_pre_topc(u1_struct_0(B_938),u1_pre_topc(B_938))))))
      | ~ v1_funct_2(D_936,u1_struct_0(A_937),u1_struct_0(g1_pre_topc(u1_struct_0(B_938),u1_pre_topc(B_938))))
      | ~ m1_subset_1(D_936,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_937),u1_struct_0(B_938))))
      | ~ v1_funct_2(D_936,u1_struct_0(A_937),u1_struct_0(B_938))
      | ~ v1_funct_1(D_936)
      | ~ l1_pre_topc(B_938)
      | ~ v2_pre_topc(B_938)
      | ~ l1_pre_topc(A_937)
      | ~ v2_pre_topc(A_937) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_5287,plain,(
    ! [A_937,B_938] :
      ( v5_pre_topc('#skF_4',A_937,B_938)
      | ~ v5_pre_topc('#skF_4',A_937,g1_pre_topc(u1_struct_0(B_938),u1_pre_topc(B_938)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_937),u1_struct_0(g1_pre_topc(u1_struct_0(B_938),u1_pre_topc(B_938))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_937),u1_struct_0(B_938))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_937),u1_struct_0(B_938))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_938)
      | ~ v2_pre_topc(B_938)
      | ~ l1_pre_topc(A_937)
      | ~ v2_pre_topc(A_937) ) ),
    inference(resolution,[status(thm)],[c_4507,c_5266])).

tff(c_5771,plain,(
    ! [A_997,B_998] :
      ( v5_pre_topc('#skF_4',A_997,B_998)
      | ~ v5_pre_topc('#skF_4',A_997,g1_pre_topc(u1_struct_0(B_998),u1_pre_topc(B_998)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),u1_struct_0(g1_pre_topc(u1_struct_0(B_998),u1_pre_topc(B_998))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),u1_struct_0(B_998))
      | ~ l1_pre_topc(B_998)
      | ~ v2_pre_topc(B_998)
      | ~ l1_pre_topc(A_997)
      | ~ v2_pre_topc(A_997) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_5287])).

tff(c_5821,plain,(
    ! [A_1000,B_1001] :
      ( v5_pre_topc('#skF_4',A_1000,B_1001)
      | ~ v5_pre_topc('#skF_4',A_1000,g1_pre_topc(u1_struct_0(B_1001),u1_pre_topc(B_1001)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1000),u1_struct_0(B_1001))
      | ~ l1_pre_topc(B_1001)
      | ~ v2_pre_topc(B_1001)
      | ~ l1_pre_topc(A_1000)
      | ~ v2_pre_topc(A_1000)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_1000)) ) ),
    inference(resolution,[status(thm)],[c_4704,c_5771])).

tff(c_5837,plain,(
    ! [A_1000] :
      ( v5_pre_topc('#skF_4',A_1000,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1000,g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1000),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_1000)
      | ~ v2_pre_topc(A_1000)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_1000)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5227,c_5821])).

tff(c_5870,plain,(
    ! [A_1002] :
      ( v5_pre_topc('#skF_4',A_1002,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1002,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1002),'#skF_4')
      | ~ l1_pre_topc(A_1002)
      | ~ v2_pre_topc(A_1002)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_1002)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5565,c_5314,c_5227,c_5466,c_5837])).

tff(c_5783,plain,(
    ! [A_997] :
      ( v5_pre_topc('#skF_4',A_997,'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_997,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_997)
      | ~ v2_pre_topc(A_997) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5227,c_5771])).

tff(c_5794,plain,(
    ! [A_997] :
      ( v5_pre_topc('#skF_4',A_997,'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_997,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc(A_997)
      | ~ v2_pre_topc(A_997) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_5783])).

tff(c_5943,plain,(
    ! [A_1006] :
      ( v5_pre_topc('#skF_4',A_1006,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1006),u1_struct_0('#skF_3'))
      | ~ v5_pre_topc('#skF_4',A_1006,g1_pre_topc('#skF_4','#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1006),'#skF_4')
      | ~ l1_pre_topc(A_1006)
      | ~ v2_pre_topc(A_1006)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_1006)) ) ),
    inference(resolution,[status(thm)],[c_5870,c_5794])).

tff(c_5952,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_5943])).

tff(c_5958,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4890,c_86,c_84,c_5952])).

tff(c_5959,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc('#skF_4','#skF_4'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_4518,c_5958])).

tff(c_5960,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5959])).

tff(c_5963,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4704,c_5960])).

tff(c_5967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4890,c_5963])).

tff(c_5969,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_5959])).

tff(c_5229,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5227,c_98])).

tff(c_5398,plain,(
    ! [D_959,A_960,B_961] :
      ( v5_pre_topc(D_959,A_960,B_961)
      | ~ v5_pre_topc(D_959,g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960)),B_961)
      | ~ m1_subset_1(D_959,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960))),u1_struct_0(B_961))))
      | ~ v1_funct_2(D_959,u1_struct_0(g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960))),u1_struct_0(B_961))
      | ~ m1_subset_1(D_959,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_960),u1_struct_0(B_961))))
      | ~ v1_funct_2(D_959,u1_struct_0(A_960),u1_struct_0(B_961))
      | ~ v1_funct_1(D_959)
      | ~ l1_pre_topc(B_961)
      | ~ v2_pre_topc(B_961)
      | ~ l1_pre_topc(A_960)
      | ~ v2_pre_topc(A_960) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_5419,plain,(
    ! [A_960,B_961] :
      ( v5_pre_topc('#skF_4',A_960,B_961)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960)),B_961)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_960),u1_pre_topc(A_960))),u1_struct_0(B_961))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_960),u1_struct_0(B_961))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_960),u1_struct_0(B_961))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_961)
      | ~ v2_pre_topc(B_961)
      | ~ l1_pre_topc(A_960)
      | ~ v2_pre_topc(A_960) ) ),
    inference(resolution,[status(thm)],[c_4507,c_5398])).

tff(c_5618,plain,(
    ! [A_984,B_985] :
      ( v5_pre_topc('#skF_4',A_984,B_985)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984)),B_985)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984))),u1_struct_0(B_985))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_984),u1_struct_0(B_985))
      | ~ l1_pre_topc(B_985)
      | ~ v2_pre_topc(B_985)
      | ~ l1_pre_topc(A_984)
      | ~ v2_pre_topc(A_984) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_5419])).

tff(c_5630,plain,(
    ! [A_984] :
      ( v5_pre_topc('#skF_4',A_984,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984)),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_984),u1_pre_topc(A_984))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_984),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_984)
      | ~ v2_pre_topc(A_984) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5227,c_5618])).

tff(c_6364,plain,(
    ! [A_1023] :
      ( v5_pre_topc('#skF_4',A_1023,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1023),u1_pre_topc(A_1023)),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1023),u1_pre_topc(A_1023))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1023),'#skF_4')
      | ~ l1_pre_topc(A_1023)
      | ~ v2_pre_topc(A_1023) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5565,c_5314,c_5227,c_5630])).

tff(c_6396,plain,
    ( v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4584,c_6364])).

tff(c_6416,plain,(
    v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_5969,c_5229,c_6396])).

tff(c_5795,plain,(
    ! [A_997,B_998] :
      ( v5_pre_topc('#skF_4',A_997,B_998)
      | ~ v5_pre_topc('#skF_4',A_997,g1_pre_topc(u1_struct_0(B_998),u1_pre_topc(B_998)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_997),u1_struct_0(B_998))
      | ~ l1_pre_topc(B_998)
      | ~ v2_pre_topc(B_998)
      | ~ l1_pre_topc(A_997)
      | ~ v2_pre_topc(A_997)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_997)) ) ),
    inference(resolution,[status(thm)],[c_4704,c_5771])).

tff(c_6422,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_6416,c_5795])).

tff(c_6435,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4890,c_86,c_84,c_82,c_80,c_76,c_6422])).

tff(c_6437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4518,c_6435])).

tff(c_6438,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4889])).

tff(c_6443,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6438,c_76])).

tff(c_7919,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6438,c_4888])).

tff(c_7920,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_7919])).

tff(c_4509,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4498,c_4498,c_6])).

tff(c_7934,plain,(
    ! [D_1168,A_1169,B_1170] :
      ( v5_pre_topc(D_1168,A_1169,B_1170)
      | ~ v5_pre_topc(D_1168,g1_pre_topc(u1_struct_0(A_1169),u1_pre_topc(A_1169)),B_1170)
      | ~ m1_subset_1(D_1168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1169),u1_pre_topc(A_1169))),u1_struct_0(B_1170))))
      | ~ v1_funct_2(D_1168,u1_struct_0(g1_pre_topc(u1_struct_0(A_1169),u1_pre_topc(A_1169))),u1_struct_0(B_1170))
      | ~ m1_subset_1(D_1168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1169),u1_struct_0(B_1170))))
      | ~ v1_funct_2(D_1168,u1_struct_0(A_1169),u1_struct_0(B_1170))
      | ~ v1_funct_1(D_1168)
      | ~ l1_pre_topc(B_1170)
      | ~ v2_pre_topc(B_1170)
      | ~ l1_pre_topc(A_1169)
      | ~ v2_pre_topc(A_1169) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_7940,plain,(
    ! [D_1168,A_1169] :
      ( v5_pre_topc(D_1168,A_1169,'#skF_3')
      | ~ v5_pre_topc(D_1168,g1_pre_topc(u1_struct_0(A_1169),u1_pre_topc(A_1169)),'#skF_3')
      | ~ m1_subset_1(D_1168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1169),u1_pre_topc(A_1169))),'#skF_4')))
      | ~ v1_funct_2(D_1168,u1_struct_0(g1_pre_topc(u1_struct_0(A_1169),u1_pre_topc(A_1169))),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_1168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1169),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(D_1168,u1_struct_0(A_1169),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(D_1168)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1169)
      | ~ v2_pre_topc(A_1169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6438,c_7934])).

tff(c_8024,plain,(
    ! [D_1183,A_1184] :
      ( v5_pre_topc(D_1183,A_1184,'#skF_3')
      | ~ v5_pre_topc(D_1183,g1_pre_topc(u1_struct_0(A_1184),u1_pre_topc(A_1184)),'#skF_3')
      | ~ v1_funct_2(D_1183,u1_struct_0(g1_pre_topc(u1_struct_0(A_1184),u1_pre_topc(A_1184))),'#skF_4')
      | ~ m1_subset_1(D_1183,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2(D_1183,u1_struct_0(A_1184),'#skF_4')
      | ~ v1_funct_1(D_1183)
      | ~ l1_pre_topc(A_1184)
      | ~ v2_pre_topc(A_1184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_6438,c_4509,c_6438,c_6438,c_4509,c_7940])).

tff(c_8031,plain,(
    ! [A_1184] :
      ( v5_pre_topc('#skF_4',A_1184,'#skF_3')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1184),u1_pre_topc(A_1184)),'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1184),'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(A_1184)
      | ~ v2_pre_topc(A_1184)
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1184),u1_pre_topc(A_1184)))) ) ),
    inference(resolution,[status(thm)],[c_4704,c_8024])).

tff(c_8241,plain,(
    ! [A_1224] :
      ( v5_pre_topc('#skF_4',A_1224,'#skF_3')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1224),u1_pre_topc(A_1224)),'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1224),'#skF_4')
      | ~ l1_pre_topc(A_1224)
      | ~ v2_pre_topc(A_1224)
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1224),u1_pre_topc(A_1224)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_8031])).

tff(c_8244,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_7920,c_8241])).

tff(c_8250,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_6443,c_8244])).

tff(c_8251,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_4518,c_8250])).

tff(c_6440,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6438,c_4584])).

tff(c_6442,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6438,c_98])).

tff(c_7890,plain,(
    ! [D_1164,A_1165,B_1166] :
      ( v5_pre_topc(D_1164,A_1165,B_1166)
      | ~ v5_pre_topc(D_1164,A_1165,g1_pre_topc(u1_struct_0(B_1166),u1_pre_topc(B_1166)))
      | ~ m1_subset_1(D_1164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165),u1_struct_0(g1_pre_topc(u1_struct_0(B_1166),u1_pre_topc(B_1166))))))
      | ~ v1_funct_2(D_1164,u1_struct_0(A_1165),u1_struct_0(g1_pre_topc(u1_struct_0(B_1166),u1_pre_topc(B_1166))))
      | ~ m1_subset_1(D_1164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165),u1_struct_0(B_1166))))
      | ~ v1_funct_2(D_1164,u1_struct_0(A_1165),u1_struct_0(B_1166))
      | ~ v1_funct_1(D_1164)
      | ~ l1_pre_topc(B_1166)
      | ~ v2_pre_topc(B_1166)
      | ~ l1_pre_topc(A_1165)
      | ~ v2_pre_topc(A_1165) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_7908,plain,(
    ! [A_1165,B_1166] :
      ( v5_pre_topc('#skF_4',A_1165,B_1166)
      | ~ v5_pre_topc('#skF_4',A_1165,g1_pre_topc(u1_struct_0(B_1166),u1_pre_topc(B_1166)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1165),u1_struct_0(g1_pre_topc(u1_struct_0(B_1166),u1_pre_topc(B_1166))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165),u1_struct_0(B_1166))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1165),u1_struct_0(B_1166))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1166)
      | ~ v2_pre_topc(B_1166)
      | ~ l1_pre_topc(A_1165)
      | ~ v2_pre_topc(A_1165) ) ),
    inference(resolution,[status(thm)],[c_4507,c_7890])).

tff(c_8301,plain,(
    ! [A_1231,B_1232] :
      ( v5_pre_topc('#skF_4',A_1231,B_1232)
      | ~ v5_pre_topc('#skF_4',A_1231,g1_pre_topc(u1_struct_0(B_1232),u1_pre_topc(B_1232)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1231),u1_struct_0(g1_pre_topc(u1_struct_0(B_1232),u1_pre_topc(B_1232))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1231),u1_struct_0(B_1232))
      | ~ l1_pre_topc(B_1232)
      | ~ v2_pre_topc(B_1232)
      | ~ l1_pre_topc(A_1231)
      | ~ v2_pre_topc(A_1231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_7908])).

tff(c_8307,plain,(
    ! [A_1231] :
      ( v5_pre_topc('#skF_4',A_1231,'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1231,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1231),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1231),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1231)
      | ~ v2_pre_topc(A_1231) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6438,c_8301])).

tff(c_8316,plain,(
    ! [A_1233] :
      ( v5_pre_topc('#skF_4',A_1233,'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1233,g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1233),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1233),'#skF_4')
      | ~ l1_pre_topc(A_1233)
      | ~ v2_pre_topc(A_1233) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_6438,c_6438,c_8307])).

tff(c_8319,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6442,c_8316])).

tff(c_8328,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6440,c_8319])).

tff(c_8329,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_8251,c_8328])).

tff(c_8333,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_8329])).

tff(c_8336,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_8333])).

tff(c_8340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_8336])).

tff(c_8341,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_8329])).

tff(c_8353,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8341])).

tff(c_8356,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_4704,c_8353])).

tff(c_8360,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7920,c_8356])).

tff(c_8361,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_8341])).

tff(c_8365,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4581,c_8361])).

tff(c_8369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8365])).

tff(c_8370,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7919])).

tff(c_8400,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8370,c_6442])).

tff(c_8684,plain,(
    ! [A_1251,B_1252] :
      ( v5_pre_topc('#skF_4',A_1251,B_1252)
      | ~ v5_pre_topc('#skF_4',A_1251,g1_pre_topc(u1_struct_0(B_1252),u1_pre_topc(B_1252)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1251),u1_struct_0(g1_pre_topc(u1_struct_0(B_1252),u1_pre_topc(B_1252))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1251),u1_struct_0(B_1252))
      | ~ l1_pre_topc(B_1252)
      | ~ v2_pre_topc(B_1252)
      | ~ l1_pre_topc(A_1251)
      | ~ v2_pre_topc(A_1251) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_7908])).

tff(c_8699,plain,(
    ! [A_1251] :
      ( v5_pre_topc('#skF_4',A_1251,'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1251,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1251),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1251),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1251)
      | ~ v2_pre_topc(A_1251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6438,c_8684])).

tff(c_8799,plain,(
    ! [A_1271] :
      ( v5_pre_topc('#skF_4',A_1271,'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1271,g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1271),'#skF_4')
      | ~ l1_pre_topc(A_1271)
      | ~ v2_pre_topc(A_1271) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_6438,c_8370,c_6438,c_8699])).

tff(c_8802,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6440,c_8799])).

tff(c_8805,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8400,c_8802])).

tff(c_8927,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_8805])).

tff(c_8930,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_8927])).

tff(c_8934,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_8930])).

tff(c_8935,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8805])).

tff(c_8960,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_8935])).

tff(c_8963,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4581,c_8960])).

tff(c_8967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8963])).

tff(c_8968,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_8935])).

tff(c_8372,plain,(
    ! [D_1235,A_1236,B_1237] :
      ( v5_pre_topc(D_1235,A_1236,B_1237)
      | ~ v5_pre_topc(D_1235,g1_pre_topc(u1_struct_0(A_1236),u1_pre_topc(A_1236)),B_1237)
      | ~ m1_subset_1(D_1235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1236),u1_pre_topc(A_1236))),u1_struct_0(B_1237))))
      | ~ v1_funct_2(D_1235,u1_struct_0(g1_pre_topc(u1_struct_0(A_1236),u1_pre_topc(A_1236))),u1_struct_0(B_1237))
      | ~ m1_subset_1(D_1235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1236),u1_struct_0(B_1237))))
      | ~ v1_funct_2(D_1235,u1_struct_0(A_1236),u1_struct_0(B_1237))
      | ~ v1_funct_1(D_1235)
      | ~ l1_pre_topc(B_1237)
      | ~ v2_pre_topc(B_1237)
      | ~ l1_pre_topc(A_1236)
      | ~ v2_pre_topc(A_1236) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_8390,plain,(
    ! [A_1236,B_1237] :
      ( v5_pre_topc('#skF_4',A_1236,B_1237)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1236),u1_pre_topc(A_1236)),B_1237)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1236),u1_pre_topc(A_1236))),u1_struct_0(B_1237))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1236),u1_struct_0(B_1237))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1236),u1_struct_0(B_1237))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1237)
      | ~ v2_pre_topc(B_1237)
      | ~ l1_pre_topc(A_1236)
      | ~ v2_pre_topc(A_1236) ) ),
    inference(resolution,[status(thm)],[c_4507,c_8372])).

tff(c_8569,plain,(
    ! [A_1245,B_1246] :
      ( v5_pre_topc('#skF_4',A_1245,B_1246)
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1245),u1_pre_topc(A_1245)),B_1246)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1245),u1_pre_topc(A_1245))),u1_struct_0(B_1246))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1245),u1_struct_0(B_1246))
      | ~ l1_pre_topc(B_1246)
      | ~ v2_pre_topc(B_1246)
      | ~ l1_pre_topc(A_1245)
      | ~ v2_pre_topc(A_1245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_8390])).

tff(c_8581,plain,(
    ! [A_1245] :
      ( v5_pre_topc('#skF_4',A_1245,'#skF_3')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1245),u1_pre_topc(A_1245)),'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1245),u1_pre_topc(A_1245))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1245),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1245)
      | ~ v2_pre_topc(A_1245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6438,c_8569])).

tff(c_9136,plain,(
    ! [A_1307] :
      ( v5_pre_topc('#skF_4',A_1307,'#skF_3')
      | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1307),u1_pre_topc(A_1307)),'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1307),u1_pre_topc(A_1307))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1307),'#skF_4')
      | ~ l1_pre_topc(A_1307)
      | ~ v2_pre_topc(A_1307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_6438,c_8581])).

tff(c_9142,plain,
    ( v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8400,c_9136])).

tff(c_9156,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_6443,c_8968,c_9142])).

tff(c_9158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4518,c_9156])).

tff(c_9160,plain,(
    v5_pre_topc('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_9360,plain,(
    ! [C_1369,A_1370,B_1371] :
      ( v1_funct_2(C_1369,A_1370,B_1371)
      | ~ v1_partfun1(C_1369,A_1370)
      | ~ v1_funct_1(C_1369)
      | ~ m1_subset_1(C_1369,k1_zfmisc_1(k2_zfmisc_1(A_1370,B_1371))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_9364,plain,(
    ! [A_1370,B_1371] :
      ( v1_funct_2('#skF_4',A_1370,B_1371)
      | ~ v1_partfun1('#skF_4',A_1370)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4507,c_9360])).

tff(c_9373,plain,(
    ! [A_1370,B_1371] :
      ( v1_funct_2('#skF_4',A_1370,B_1371)
      | ~ v1_partfun1('#skF_4',A_1370) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_9364])).

tff(c_11053,plain,(
    ! [D_1544,A_1545,B_1546] :
      ( v5_pre_topc(D_1544,A_1545,g1_pre_topc(u1_struct_0(B_1546),u1_pre_topc(B_1546)))
      | ~ v5_pre_topc(D_1544,A_1545,B_1546)
      | ~ m1_subset_1(D_1544,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1545),u1_struct_0(g1_pre_topc(u1_struct_0(B_1546),u1_pre_topc(B_1546))))))
      | ~ v1_funct_2(D_1544,u1_struct_0(A_1545),u1_struct_0(g1_pre_topc(u1_struct_0(B_1546),u1_pre_topc(B_1546))))
      | ~ m1_subset_1(D_1544,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1545),u1_struct_0(B_1546))))
      | ~ v1_funct_2(D_1544,u1_struct_0(A_1545),u1_struct_0(B_1546))
      | ~ v1_funct_1(D_1544)
      | ~ l1_pre_topc(B_1546)
      | ~ v2_pre_topc(B_1546)
      | ~ l1_pre_topc(A_1545)
      | ~ v2_pre_topc(A_1545) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_11074,plain,(
    ! [A_1545,B_1546] :
      ( v5_pre_topc('#skF_4',A_1545,g1_pre_topc(u1_struct_0(B_1546),u1_pre_topc(B_1546)))
      | ~ v5_pre_topc('#skF_4',A_1545,B_1546)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1545),u1_struct_0(g1_pre_topc(u1_struct_0(B_1546),u1_pre_topc(B_1546))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1545),u1_struct_0(B_1546))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1545),u1_struct_0(B_1546))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1546)
      | ~ v2_pre_topc(B_1546)
      | ~ l1_pre_topc(A_1545)
      | ~ v2_pre_topc(A_1545) ) ),
    inference(resolution,[status(thm)],[c_4507,c_11053])).

tff(c_11370,plain,(
    ! [A_1579,B_1580] :
      ( v5_pre_topc('#skF_4',A_1579,g1_pre_topc(u1_struct_0(B_1580),u1_pre_topc(B_1580)))
      | ~ v5_pre_topc('#skF_4',A_1579,B_1580)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1579),u1_struct_0(g1_pre_topc(u1_struct_0(B_1580),u1_pre_topc(B_1580))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1579),u1_struct_0(B_1580))
      | ~ l1_pre_topc(B_1580)
      | ~ v2_pre_topc(B_1580)
      | ~ l1_pre_topc(A_1579)
      | ~ v2_pre_topc(A_1579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_11074])).

tff(c_11389,plain,(
    ! [A_1579,B_1580] :
      ( v5_pre_topc('#skF_4',A_1579,g1_pre_topc(u1_struct_0(B_1580),u1_pre_topc(B_1580)))
      | ~ v5_pre_topc('#skF_4',A_1579,B_1580)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1579),u1_struct_0(B_1580))
      | ~ l1_pre_topc(B_1580)
      | ~ v2_pre_topc(B_1580)
      | ~ l1_pre_topc(A_1579)
      | ~ v2_pre_topc(A_1579)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_1579)) ) ),
    inference(resolution,[status(thm)],[c_9373,c_11370])).

tff(c_9567,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_98,c_9556])).

tff(c_9570,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_9567])).

tff(c_9621,plain,(
    ! [D_1426,A_1427,B_1428] :
      ( v5_pre_topc(D_1426,g1_pre_topc(u1_struct_0(A_1427),u1_pre_topc(A_1427)),B_1428)
      | ~ v5_pre_topc(D_1426,A_1427,B_1428)
      | ~ m1_subset_1(D_1426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1427),u1_pre_topc(A_1427))),u1_struct_0(B_1428))))
      | ~ v1_funct_2(D_1426,u1_struct_0(g1_pre_topc(u1_struct_0(A_1427),u1_pre_topc(A_1427))),u1_struct_0(B_1428))
      | ~ m1_subset_1(D_1426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1427),u1_struct_0(B_1428))))
      | ~ v1_funct_2(D_1426,u1_struct_0(A_1427),u1_struct_0(B_1428))
      | ~ v1_funct_1(D_1426)
      | ~ l1_pre_topc(B_1428)
      | ~ v2_pre_topc(B_1428)
      | ~ l1_pre_topc(A_1427)
      | ~ v2_pre_topc(A_1427) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_9633,plain,(
    ! [A_1427,B_1428] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1427),u1_pre_topc(A_1427)),B_1428)
      | ~ v5_pre_topc('#skF_4',A_1427,B_1428)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1427),u1_pre_topc(A_1427))),u1_struct_0(B_1428))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1427),u1_struct_0(B_1428))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1427),u1_struct_0(B_1428))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1428)
      | ~ v2_pre_topc(B_1428)
      | ~ l1_pre_topc(A_1427)
      | ~ v2_pre_topc(A_1427) ) ),
    inference(resolution,[status(thm)],[c_4507,c_9621])).

tff(c_9711,plain,(
    ! [A_1450,B_1451] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1450),u1_pre_topc(A_1450)),B_1451)
      | ~ v5_pre_topc('#skF_4',A_1450,B_1451)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1450),u1_pre_topc(A_1450))),u1_struct_0(B_1451))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1450),u1_struct_0(B_1451))
      | ~ l1_pre_topc(B_1451)
      | ~ v2_pre_topc(B_1451)
      | ~ l1_pre_topc(A_1450)
      | ~ v2_pre_topc(A_1450) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_9633])).

tff(c_9734,plain,(
    ! [A_1452,B_1453] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1452),u1_pre_topc(A_1452)),B_1453)
      | ~ v5_pre_topc('#skF_4',A_1452,B_1453)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1452),u1_struct_0(B_1453))
      | ~ l1_pre_topc(B_1453)
      | ~ v2_pre_topc(B_1453)
      | ~ l1_pre_topc(A_1452)
      | ~ v2_pre_topc(A_1452)
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1452),u1_pre_topc(A_1452)))) ) ),
    inference(resolution,[status(thm)],[c_9373,c_9711])).

tff(c_9736,plain,(
    ! [B_1453] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_1453)
      | ~ v5_pre_topc('#skF_4','#skF_2',B_1453)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_1453))
      | ~ l1_pre_topc(B_1453)
      | ~ v2_pre_topc(B_1453)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_9570,c_9734])).

tff(c_9739,plain,(
    ! [B_1453] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_1453)
      | ~ v5_pre_topc('#skF_4','#skF_2',B_1453)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(B_1453))
      | ~ l1_pre_topc(B_1453)
      | ~ v2_pre_topc(B_1453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_9736])).

tff(c_9159,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_9661,plain,(
    ! [D_1441,A_1442,B_1443] :
      ( v5_pre_topc(D_1441,A_1442,B_1443)
      | ~ v5_pre_topc(D_1441,A_1442,g1_pre_topc(u1_struct_0(B_1443),u1_pre_topc(B_1443)))
      | ~ m1_subset_1(D_1441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1442),u1_struct_0(g1_pre_topc(u1_struct_0(B_1443),u1_pre_topc(B_1443))))))
      | ~ v1_funct_2(D_1441,u1_struct_0(A_1442),u1_struct_0(g1_pre_topc(u1_struct_0(B_1443),u1_pre_topc(B_1443))))
      | ~ m1_subset_1(D_1441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1442),u1_struct_0(B_1443))))
      | ~ v1_funct_2(D_1441,u1_struct_0(A_1442),u1_struct_0(B_1443))
      | ~ v1_funct_1(D_1441)
      | ~ l1_pre_topc(B_1443)
      | ~ v2_pre_topc(B_1443)
      | ~ l1_pre_topc(A_1442)
      | ~ v2_pre_topc(A_1442) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_9673,plain,(
    ! [A_1442,B_1443] :
      ( v5_pre_topc('#skF_4',A_1442,B_1443)
      | ~ v5_pre_topc('#skF_4',A_1442,g1_pre_topc(u1_struct_0(B_1443),u1_pre_topc(B_1443)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1442),u1_struct_0(g1_pre_topc(u1_struct_0(B_1443),u1_pre_topc(B_1443))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1442),u1_struct_0(B_1443))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1442),u1_struct_0(B_1443))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1443)
      | ~ v2_pre_topc(B_1443)
      | ~ l1_pre_topc(A_1442)
      | ~ v2_pre_topc(A_1442) ) ),
    inference(resolution,[status(thm)],[c_4507,c_9661])).

tff(c_9765,plain,(
    ! [A_1458,B_1459] :
      ( v5_pre_topc('#skF_4',A_1458,B_1459)
      | ~ v5_pre_topc('#skF_4',A_1458,g1_pre_topc(u1_struct_0(B_1459),u1_pre_topc(B_1459)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1458),u1_struct_0(g1_pre_topc(u1_struct_0(B_1459),u1_pre_topc(B_1459))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1458),u1_struct_0(B_1459))
      | ~ l1_pre_topc(B_1459)
      | ~ v2_pre_topc(B_1459)
      | ~ l1_pre_topc(A_1458)
      | ~ v2_pre_topc(A_1458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_9673])).

tff(c_9776,plain,(
    ! [A_1460,B_1461] :
      ( v5_pre_topc('#skF_4',A_1460,B_1461)
      | ~ v5_pre_topc('#skF_4',A_1460,g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461)))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1460),u1_struct_0(B_1461))
      | ~ l1_pre_topc(B_1461)
      | ~ v2_pre_topc(B_1461)
      | ~ l1_pre_topc(A_1460)
      | ~ v2_pre_topc(A_1460)
      | ~ v1_partfun1('#skF_4',u1_struct_0(A_1460)) ) ),
    inference(resolution,[status(thm)],[c_9373,c_9765])).

tff(c_9780,plain,(
    ! [B_1461] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_1461)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_1461))
      | ~ l1_pre_topc(B_1461)
      | ~ v2_pre_topc(B_1461)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))))
      | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461)))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461))) ) ),
    inference(resolution,[status(thm)],[c_9739,c_9776])).

tff(c_9783,plain,(
    ! [B_1461] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),B_1461)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(B_1461))
      | ~ l1_pre_topc(B_1461)
      | ~ v2_pre_topc(B_1461)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461)))
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(B_1461),u1_pre_topc(B_1461))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9570,c_9780])).

tff(c_9784,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9783])).

tff(c_9787,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_9784])).

tff(c_9791,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_9787])).

tff(c_9793,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_9783])).

tff(c_9740,plain,(
    ! [D_1454,A_1455,B_1456] :
      ( v5_pre_topc(D_1454,A_1455,g1_pre_topc(u1_struct_0(B_1456),u1_pre_topc(B_1456)))
      | ~ v5_pre_topc(D_1454,A_1455,B_1456)
      | ~ m1_subset_1(D_1454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1455),u1_struct_0(g1_pre_topc(u1_struct_0(B_1456),u1_pre_topc(B_1456))))))
      | ~ v1_funct_2(D_1454,u1_struct_0(A_1455),u1_struct_0(g1_pre_topc(u1_struct_0(B_1456),u1_pre_topc(B_1456))))
      | ~ m1_subset_1(D_1454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1455),u1_struct_0(B_1456))))
      | ~ v1_funct_2(D_1454,u1_struct_0(A_1455),u1_struct_0(B_1456))
      | ~ v1_funct_1(D_1454)
      | ~ l1_pre_topc(B_1456)
      | ~ v2_pre_topc(B_1456)
      | ~ l1_pre_topc(A_1455)
      | ~ v2_pre_topc(A_1455) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_9752,plain,(
    ! [A_1455,B_1456] :
      ( v5_pre_topc('#skF_4',A_1455,g1_pre_topc(u1_struct_0(B_1456),u1_pre_topc(B_1456)))
      | ~ v5_pre_topc('#skF_4',A_1455,B_1456)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1455),u1_struct_0(g1_pre_topc(u1_struct_0(B_1456),u1_pre_topc(B_1456))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1455),u1_struct_0(B_1456))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1455),u1_struct_0(B_1456))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1456)
      | ~ v2_pre_topc(B_1456)
      | ~ l1_pre_topc(A_1455)
      | ~ v2_pre_topc(A_1455) ) ),
    inference(resolution,[status(thm)],[c_4507,c_9740])).

tff(c_9794,plain,(
    ! [A_1462,B_1463] :
      ( v5_pre_topc('#skF_4',A_1462,g1_pre_topc(u1_struct_0(B_1463),u1_pre_topc(B_1463)))
      | ~ v5_pre_topc('#skF_4',A_1462,B_1463)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1462),u1_struct_0(g1_pre_topc(u1_struct_0(B_1463),u1_pre_topc(B_1463))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1462),u1_struct_0(B_1463))
      | ~ l1_pre_topc(B_1463)
      | ~ v2_pre_topc(B_1463)
      | ~ l1_pre_topc(A_1462)
      | ~ v2_pre_topc(A_1462) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_9752])).

tff(c_9800,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_98,c_9794])).

tff(c_9804,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9793,c_82,c_80,c_9800])).

tff(c_9805,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_9159,c_9804])).

tff(c_9806,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_9805])).

tff(c_9809,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_9253,c_9806])).

tff(c_9813,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_9809])).

tff(c_9814,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3'))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_9805])).

tff(c_9828,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9814])).

tff(c_9831,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_9739,c_9828])).

tff(c_9835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_9160,c_9831])).

tff(c_9836,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_9814])).

tff(c_9840,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_9373,c_9836])).

tff(c_9844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9570,c_9840])).

tff(c_9845,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9567])).

tff(c_9847,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9845,c_98])).

tff(c_9868,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9845,c_9253])).

tff(c_9947,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9868])).

tff(c_9950,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_9253,c_9947])).

tff(c_9954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_9950])).

tff(c_9956,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_9868])).

tff(c_9862,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9845,c_54])).

tff(c_11265,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_4',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9956,c_9862])).

tff(c_11266,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_11265])).

tff(c_11269,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_11266])).

tff(c_11273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11269])).

tff(c_11275,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_11265])).

tff(c_9957,plain,(
    ! [D_1478,A_1479,B_1480] :
      ( v5_pre_topc(D_1478,g1_pre_topc(u1_struct_0(A_1479),u1_pre_topc(A_1479)),B_1480)
      | ~ v5_pre_topc(D_1478,A_1479,B_1480)
      | ~ m1_subset_1(D_1478,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1479),u1_pre_topc(A_1479))),u1_struct_0(B_1480))))
      | ~ v1_funct_2(D_1478,u1_struct_0(g1_pre_topc(u1_struct_0(A_1479),u1_pre_topc(A_1479))),u1_struct_0(B_1480))
      | ~ m1_subset_1(D_1478,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1479),u1_struct_0(B_1480))))
      | ~ v1_funct_2(D_1478,u1_struct_0(A_1479),u1_struct_0(B_1480))
      | ~ v1_funct_1(D_1478)
      | ~ l1_pre_topc(B_1480)
      | ~ v2_pre_topc(B_1480)
      | ~ l1_pre_topc(A_1479)
      | ~ v2_pre_topc(A_1479) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_9978,plain,(
    ! [A_1479,B_1480] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1479),u1_pre_topc(A_1479)),B_1480)
      | ~ v5_pre_topc('#skF_4',A_1479,B_1480)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1479),u1_pre_topc(A_1479))),u1_struct_0(B_1480))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1479),u1_struct_0(B_1480))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1479),u1_struct_0(B_1480))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1480)
      | ~ v2_pre_topc(B_1480)
      | ~ l1_pre_topc(A_1479)
      | ~ v2_pre_topc(A_1479) ) ),
    inference(resolution,[status(thm)],[c_4507,c_9957])).

tff(c_11312,plain,(
    ! [A_1572,B_1573] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1572),u1_pre_topc(A_1572)),B_1573)
      | ~ v5_pre_topc('#skF_4',A_1572,B_1573)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1572),u1_pre_topc(A_1572))),u1_struct_0(B_1573))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1572),u1_struct_0(B_1573))
      | ~ l1_pre_topc(B_1573)
      | ~ v2_pre_topc(B_1573)
      | ~ l1_pre_topc(A_1572)
      | ~ v2_pre_topc(A_1572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_9978])).

tff(c_11321,plain,(
    ! [A_1572] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1572),u1_pre_topc(A_1572)),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1572,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1572),u1_pre_topc(A_1572))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1572),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_1572)
      | ~ v2_pre_topc(A_1572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9845,c_11312])).

tff(c_11543,plain,(
    ! [A_1593] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1593),u1_pre_topc(A_1593)),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1593,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1593),u1_pre_topc(A_1593))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1593),'#skF_4')
      | ~ l1_pre_topc(A_1593)
      | ~ v2_pre_topc(A_1593) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11275,c_9956,c_9845,c_11321])).

tff(c_11558,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_11543,c_9159])).

tff(c_11574,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_9847,c_11558])).

tff(c_11577,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_11574])).

tff(c_11580,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9373,c_11577])).

tff(c_11584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9569,c_11580])).

tff(c_11585,plain,(
    ~ v5_pre_topc('#skF_4','#skF_2',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_11574])).

tff(c_11607,plain,
    ( ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_11389,c_11585])).

tff(c_11614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9569,c_86,c_84,c_82,c_80,c_76,c_9160,c_11607])).

tff(c_11615,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9568])).

tff(c_13142,plain,
    ( u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))) = '#skF_4'
    | v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11615,c_9567])).

tff(c_13143,plain,(
    v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_13142])).

tff(c_11617,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11615,c_9159])).

tff(c_11620,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11615,c_76])).

tff(c_13207,plain,(
    ! [D_1737,A_1738,B_1739] :
      ( v5_pre_topc(D_1737,g1_pre_topc(u1_struct_0(A_1738),u1_pre_topc(A_1738)),B_1739)
      | ~ v5_pre_topc(D_1737,A_1738,B_1739)
      | ~ m1_subset_1(D_1737,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1738),u1_pre_topc(A_1738))),u1_struct_0(B_1739))))
      | ~ v1_funct_2(D_1737,u1_struct_0(g1_pre_topc(u1_struct_0(A_1738),u1_pre_topc(A_1738))),u1_struct_0(B_1739))
      | ~ m1_subset_1(D_1737,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1738),u1_struct_0(B_1739))))
      | ~ v1_funct_2(D_1737,u1_struct_0(A_1738),u1_struct_0(B_1739))
      | ~ v1_funct_1(D_1737)
      | ~ l1_pre_topc(B_1739)
      | ~ v2_pre_topc(B_1739)
      | ~ l1_pre_topc(A_1738)
      | ~ v2_pre_topc(A_1738) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_13225,plain,(
    ! [A_1738,B_1739] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1738),u1_pre_topc(A_1738)),B_1739)
      | ~ v5_pre_topc('#skF_4',A_1738,B_1739)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1738),u1_pre_topc(A_1738))),u1_struct_0(B_1739))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1738),u1_struct_0(B_1739))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1738),u1_struct_0(B_1739))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1739)
      | ~ v2_pre_topc(B_1739)
      | ~ l1_pre_topc(A_1738)
      | ~ v2_pre_topc(A_1738) ) ),
    inference(resolution,[status(thm)],[c_4507,c_13207])).

tff(c_13407,plain,(
    ! [A_1777,B_1778] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1777),u1_pre_topc(A_1777)),B_1778)
      | ~ v5_pre_topc('#skF_4',A_1777,B_1778)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1777),u1_pre_topc(A_1777))),u1_struct_0(B_1778))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1777),u1_struct_0(B_1778))
      | ~ l1_pre_topc(B_1778)
      | ~ v2_pre_topc(B_1778)
      | ~ l1_pre_topc(A_1777)
      | ~ v2_pre_topc(A_1777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_13225])).

tff(c_13416,plain,(
    ! [A_1777] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1777),u1_pre_topc(A_1777)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1777,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1777),u1_pre_topc(A_1777))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1777),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1777)
      | ~ v2_pre_topc(A_1777) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11615,c_13407])).

tff(c_13466,plain,(
    ! [A_1782] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1782),u1_pre_topc(A_1782)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1782,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1782),u1_pre_topc(A_1782))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1782),'#skF_4')
      | ~ l1_pre_topc(A_1782)
      | ~ v2_pre_topc(A_1782) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11615,c_13416])).

tff(c_13476,plain,(
    ! [A_1783] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1783),u1_pre_topc(A_1783)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1783,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1783),'#skF_4')
      | ~ l1_pre_topc(A_1783)
      | ~ v2_pre_topc(A_1783)
      | ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1783),u1_pre_topc(A_1783)))) ) ),
    inference(resolution,[status(thm)],[c_9373,c_13466])).

tff(c_13479,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_13143,c_13476])).

tff(c_13485,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_11620,c_9160,c_13479])).

tff(c_11619,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11615,c_98])).

tff(c_11672,plain,(
    ! [D_1594,A_1595,B_1596] :
      ( v5_pre_topc(D_1594,A_1595,g1_pre_topc(u1_struct_0(B_1596),u1_pre_topc(B_1596)))
      | ~ v5_pre_topc(D_1594,A_1595,B_1596)
      | ~ m1_subset_1(D_1594,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1595),u1_struct_0(g1_pre_topc(u1_struct_0(B_1596),u1_pre_topc(B_1596))))))
      | ~ v1_funct_2(D_1594,u1_struct_0(A_1595),u1_struct_0(g1_pre_topc(u1_struct_0(B_1596),u1_pre_topc(B_1596))))
      | ~ m1_subset_1(D_1594,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1595),u1_struct_0(B_1596))))
      | ~ v1_funct_2(D_1594,u1_struct_0(A_1595),u1_struct_0(B_1596))
      | ~ v1_funct_1(D_1594)
      | ~ l1_pre_topc(B_1596)
      | ~ v2_pre_topc(B_1596)
      | ~ l1_pre_topc(A_1595)
      | ~ v2_pre_topc(A_1595) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_11690,plain,(
    ! [A_1595,B_1596] :
      ( v5_pre_topc('#skF_4',A_1595,g1_pre_topc(u1_struct_0(B_1596),u1_pre_topc(B_1596)))
      | ~ v5_pre_topc('#skF_4',A_1595,B_1596)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1595),u1_struct_0(g1_pre_topc(u1_struct_0(B_1596),u1_pre_topc(B_1596))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1595),u1_struct_0(B_1596))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1595),u1_struct_0(B_1596))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1596)
      | ~ v2_pre_topc(B_1596)
      | ~ l1_pre_topc(A_1595)
      | ~ v2_pre_topc(A_1595) ) ),
    inference(resolution,[status(thm)],[c_4507,c_11672])).

tff(c_13498,plain,(
    ! [A_1786,B_1787] :
      ( v5_pre_topc('#skF_4',A_1786,g1_pre_topc(u1_struct_0(B_1787),u1_pre_topc(B_1787)))
      | ~ v5_pre_topc('#skF_4',A_1786,B_1787)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1786),u1_struct_0(g1_pre_topc(u1_struct_0(B_1787),u1_pre_topc(B_1787))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1786),u1_struct_0(B_1787))
      | ~ l1_pre_topc(B_1787)
      | ~ v2_pre_topc(B_1787)
      | ~ l1_pre_topc(A_1786)
      | ~ v2_pre_topc(A_1786) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_11690])).

tff(c_13504,plain,(
    ! [A_1786] :
      ( v5_pre_topc('#skF_4',A_1786,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1786,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1786),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1786),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1786)
      | ~ v2_pre_topc(A_1786) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11615,c_13498])).

tff(c_13534,plain,(
    ! [A_1789] :
      ( v5_pre_topc('#skF_4',A_1789,g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1789,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1789),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1789),'#skF_4')
      | ~ l1_pre_topc(A_1789)
      | ~ v2_pre_topc(A_1789) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11615,c_11615,c_13504])).

tff(c_13537,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_11619,c_13534])).

tff(c_13546,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13485,c_13537])).

tff(c_13547,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_11617,c_13546])).

tff(c_13551,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_13547])).

tff(c_13564,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_13551])).

tff(c_13568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_13564])).

tff(c_13569,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_13547])).

tff(c_13571,plain,(
    ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_13569])).

tff(c_13574,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_9373,c_13571])).

tff(c_13578,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13143,c_13574])).

tff(c_13579,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_13569])).

tff(c_13583,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_9253,c_13579])).

tff(c_13587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_13583])).

tff(c_13588,plain,(
    u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_13142])).

tff(c_13618,plain,(
    v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13588,c_11619])).

tff(c_13999,plain,(
    ! [A_1828,B_1829] :
      ( v5_pre_topc('#skF_4',A_1828,g1_pre_topc(u1_struct_0(B_1829),u1_pre_topc(B_1829)))
      | ~ v5_pre_topc('#skF_4',A_1828,B_1829)
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1828),u1_struct_0(g1_pre_topc(u1_struct_0(B_1829),u1_pre_topc(B_1829))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1828),u1_struct_0(B_1829))
      | ~ l1_pre_topc(B_1829)
      | ~ v2_pre_topc(B_1829)
      | ~ l1_pre_topc(A_1828)
      | ~ v2_pre_topc(A_1828) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_11690])).

tff(c_14014,plain,(
    ! [A_1828] :
      ( v5_pre_topc('#skF_4',A_1828,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1828,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1828),u1_struct_0(g1_pre_topc('#skF_4',u1_pre_topc('#skF_3'))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1828),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1828)
      | ~ v2_pre_topc(A_1828) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11615,c_13999])).

tff(c_14081,plain,(
    ! [A_1840] :
      ( v5_pre_topc('#skF_4',A_1840,g1_pre_topc('#skF_4',u1_pre_topc('#skF_3')))
      | ~ v5_pre_topc('#skF_4',A_1840,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1840),'#skF_4')
      | ~ l1_pre_topc(A_1840)
      | ~ v2_pre_topc(A_1840) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11615,c_13588,c_11615,c_14014])).

tff(c_14088,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_14081,c_11617])).

tff(c_14094,plain,
    ( ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13618,c_14088])).

tff(c_14135,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_14094])).

tff(c_14138,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_14135])).

tff(c_14142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_14138])).

tff(c_14143,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_14094])).

tff(c_14167,plain,(
    ~ v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_14143])).

tff(c_13698,plain,(
    ! [D_1794,A_1795,B_1796] :
      ( v5_pre_topc(D_1794,g1_pre_topc(u1_struct_0(A_1795),u1_pre_topc(A_1795)),B_1796)
      | ~ v5_pre_topc(D_1794,A_1795,B_1796)
      | ~ m1_subset_1(D_1794,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1795),u1_pre_topc(A_1795))),u1_struct_0(B_1796))))
      | ~ v1_funct_2(D_1794,u1_struct_0(g1_pre_topc(u1_struct_0(A_1795),u1_pre_topc(A_1795))),u1_struct_0(B_1796))
      | ~ m1_subset_1(D_1794,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1795),u1_struct_0(B_1796))))
      | ~ v1_funct_2(D_1794,u1_struct_0(A_1795),u1_struct_0(B_1796))
      | ~ v1_funct_1(D_1794)
      | ~ l1_pre_topc(B_1796)
      | ~ v2_pre_topc(B_1796)
      | ~ l1_pre_topc(A_1795)
      | ~ v2_pre_topc(A_1795) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_13722,plain,(
    ! [A_1795,B_1796] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1795),u1_pre_topc(A_1795)),B_1796)
      | ~ v5_pre_topc('#skF_4',A_1795,B_1796)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1795),u1_pre_topc(A_1795))),u1_struct_0(B_1796))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1795),u1_struct_0(B_1796))))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1795),u1_struct_0(B_1796))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc(B_1796)
      | ~ v2_pre_topc(B_1796)
      | ~ l1_pre_topc(A_1795)
      | ~ v2_pre_topc(A_1795) ) ),
    inference(resolution,[status(thm)],[c_4507,c_13698])).

tff(c_13837,plain,(
    ! [A_1812,B_1813] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1812),u1_pre_topc(A_1812)),B_1813)
      | ~ v5_pre_topc('#skF_4',A_1812,B_1813)
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1812),u1_pre_topc(A_1812))),u1_struct_0(B_1813))
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1812),u1_struct_0(B_1813))
      | ~ l1_pre_topc(B_1813)
      | ~ v2_pre_topc(B_1813)
      | ~ l1_pre_topc(A_1812)
      | ~ v2_pre_topc(A_1812) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4507,c_13722])).

tff(c_13849,plain,(
    ! [A_1812] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1812),u1_pre_topc(A_1812)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1812,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1812),u1_pre_topc(A_1812))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1812),u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_1812)
      | ~ v2_pre_topc(A_1812) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11615,c_13837])).

tff(c_14283,plain,(
    ! [A_1853] :
      ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0(A_1853),u1_pre_topc(A_1853)),'#skF_3')
      | ~ v5_pre_topc('#skF_4',A_1853,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0(g1_pre_topc(u1_struct_0(A_1853),u1_pre_topc(A_1853))),'#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0(A_1853),'#skF_4')
      | ~ l1_pre_topc(A_1853)
      | ~ v2_pre_topc(A_1853) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_11615,c_13849])).

tff(c_14289,plain,
    ( v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3')
    | ~ v5_pre_topc('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),'#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_13618,c_14283])).

tff(c_14303,plain,(
    v5_pre_topc('#skF_4',g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_11620,c_9160,c_14289])).

tff(c_14305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14167,c_14303])).

tff(c_14306,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_14143])).

tff(c_14310,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_9253,c_14306])).

tff(c_14314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_14310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.81  
% 10.26/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.26/3.81  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_mcart_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 10.26/3.81  
% 10.26/3.81  %Foreground sorts:
% 10.26/3.81  
% 10.26/3.81  
% 10.26/3.81  %Background operators:
% 10.26/3.81  
% 10.26/3.81  
% 10.26/3.81  %Foreground operators:
% 10.26/3.81  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 10.26/3.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.26/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.26/3.81  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 10.26/3.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.26/3.81  tff('#skF_1', type, '#skF_1': $i > $i).
% 10.26/3.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.26/3.81  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 10.26/3.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.26/3.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.26/3.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.26/3.81  tff('#skF_5', type, '#skF_5': $i).
% 10.26/3.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.26/3.81  tff('#skF_2', type, '#skF_2': $i).
% 10.26/3.81  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.26/3.81  tff('#skF_3', type, '#skF_3': $i).
% 10.26/3.81  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 10.26/3.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.26/3.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.26/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.26/3.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.26/3.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.26/3.81  tff('#skF_4', type, '#skF_4': $i).
% 10.26/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.26/3.81  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 10.26/3.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.26/3.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.26/3.81  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.26/3.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.26/3.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.26/3.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.26/3.81  
% 10.45/3.87  tff(f_230, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 10.45/3.87  tff(f_134, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 10.45/3.87  tff(f_130, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 10.45/3.87  tff(f_142, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 10.45/3.87  tff(f_97, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 10.45/3.87  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 10.45/3.87  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 10.45/3.87  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.45/3.87  tff(f_124, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 10.45/3.87  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.45/3.87  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 10.45/3.87  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.45/3.87  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 10.45/3.87  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 10.45/3.87  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 10.45/3.87  tff(f_200, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 10.45/3.87  tff(f_171, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 10.45/3.87  tff(f_47, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 10.45/3.87  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 10.45/3.87  tff(f_40, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 10.45/3.87  tff(c_84, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_9246, plain, (![A_1314]: (m1_subset_1(u1_pre_topc(A_1314), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1314)))) | ~l1_pre_topc(A_1314))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.45/3.87  tff(c_48, plain, (![A_48, B_49]: (l1_pre_topc(g1_pre_topc(A_48, B_49)) | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.45/3.87  tff(c_9253, plain, (![A_1314]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_1314), u1_pre_topc(A_1314))) | ~l1_pre_topc(A_1314))), inference(resolution, [status(thm)], [c_9246, c_48])).
% 10.45/3.87  tff(c_86, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_54, plain, (![A_51]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_51), u1_pre_topc(A_51))) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_142])).
% 10.45/3.87  tff(c_76, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_34, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.45/3.87  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 10.45/3.87  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.45/3.87  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_163, plain, (![C_105, B_106, A_107]: (v5_relat_1(C_105, B_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.45/3.87  tff(c_177, plain, (v5_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_163])).
% 10.45/3.87  tff(c_66, plain, ('#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_99, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68])).
% 10.45/3.87  tff(c_28, plain, (![C_19, A_17, B_18]: (v4_relat_1(C_19, A_17) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.45/3.87  tff(c_253, plain, (v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_99, c_28])).
% 10.45/3.87  tff(c_70, plain, (v1_funct_2('#skF_5', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_98, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70])).
% 10.45/3.87  tff(c_2442, plain, (![B_502, C_503, A_504]: (k1_xboole_0=B_502 | v1_partfun1(C_503, A_504) | ~v1_funct_2(C_503, A_504, B_502) | ~m1_subset_1(C_503, k1_zfmisc_1(k2_zfmisc_1(A_504, B_502))) | ~v1_funct_1(C_503))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.45/3.87  tff(c_2451, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_2442])).
% 10.45/3.87  tff(c_2473, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_98, c_2451])).
% 10.45/3.87  tff(c_2769, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_2473])).
% 10.45/3.87  tff(c_24, plain, (![C_16, A_14, B_15]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 10.45/3.87  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_24])).
% 10.45/3.87  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.45/3.87  tff(c_18, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(B_11), A_10) | ~v4_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.45/3.87  tff(c_2296, plain, (![D_489, C_490, B_491, A_492]: (m1_subset_1(D_489, k1_zfmisc_1(k2_zfmisc_1(C_490, B_491))) | ~r1_tarski(k2_relat_1(D_489), B_491) | ~m1_subset_1(D_489, k1_zfmisc_1(k2_zfmisc_1(C_490, A_492))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.45/3.87  tff(c_2309, plain, (![B_491]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), B_491))) | ~r1_tarski(k2_relat_1('#skF_4'), B_491))), inference(resolution, [status(thm)], [c_74, c_2296])).
% 10.45/3.87  tff(c_2356, plain, (![D_495, B_496, C_497, A_498]: (m1_subset_1(D_495, k1_zfmisc_1(k2_zfmisc_1(B_496, C_497))) | ~r1_tarski(k1_relat_1(D_495), B_496) | ~m1_subset_1(D_495, k1_zfmisc_1(k2_zfmisc_1(A_498, C_497))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.45/3.87  tff(c_2618, plain, (![B_521, B_522]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_521, B_522))) | ~r1_tarski(k1_relat_1('#skF_4'), B_521) | ~r1_tarski(k2_relat_1('#skF_4'), B_522))), inference(resolution, [status(thm)], [c_2309, c_2356])).
% 10.45/3.87  tff(c_40, plain, (![C_44, A_42, B_43]: (v1_funct_2(C_44, A_42, B_43) | ~v1_partfun1(C_44, A_42) | ~v1_funct_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.45/3.87  tff(c_2632, plain, (![B_521, B_522]: (v1_funct_2('#skF_4', B_521, B_522) | ~v1_partfun1('#skF_4', B_521) | ~v1_funct_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), B_521) | ~r1_tarski(k2_relat_1('#skF_4'), B_522))), inference(resolution, [status(thm)], [c_2618, c_40])).
% 10.45/3.87  tff(c_3000, plain, (![B_560, B_561]: (v1_funct_2('#skF_4', B_560, B_561) | ~v1_partfun1('#skF_4', B_560) | ~r1_tarski(k1_relat_1('#skF_4'), B_560) | ~r1_tarski(k2_relat_1('#skF_4'), B_561))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2632])).
% 10.45/3.87  tff(c_3003, plain, (![A_10, B_561]: (v1_funct_2('#skF_4', A_10, B_561) | ~v1_partfun1('#skF_4', A_10) | ~r1_tarski(k2_relat_1('#skF_4'), B_561) | ~v4_relat_1('#skF_4', A_10) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_3000])).
% 10.45/3.87  tff(c_3059, plain, (![A_565, B_566]: (v1_funct_2('#skF_4', A_565, B_566) | ~v1_partfun1('#skF_4', A_565) | ~r1_tarski(k2_relat_1('#skF_4'), B_566) | ~v4_relat_1('#skF_4', A_565))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3003])).
% 10.45/3.87  tff(c_3062, plain, (![A_565, A_12]: (v1_funct_2('#skF_4', A_565, A_12) | ~v1_partfun1('#skF_4', A_565) | ~v4_relat_1('#skF_4', A_565) | ~v5_relat_1('#skF_4', A_12) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_3059])).
% 10.45/3.87  tff(c_3065, plain, (![A_565, A_12]: (v1_funct_2('#skF_4', A_565, A_12) | ~v1_partfun1('#skF_4', A_565) | ~v4_relat_1('#skF_4', A_565) | ~v5_relat_1('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_3062])).
% 10.45/3.87  tff(c_2308, plain, (![B_491]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), B_491))) | ~r1_tarski(k2_relat_1('#skF_4'), B_491))), inference(resolution, [status(thm)], [c_99, c_2296])).
% 10.45/3.87  tff(c_210, plain, (![A_120]: (m1_subset_1(u1_pre_topc(A_120), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_120)))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.45/3.87  tff(c_217, plain, (![A_120]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_120), u1_pre_topc(A_120))) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_210, c_48])).
% 10.45/3.87  tff(c_789, plain, (![B_224, C_225, A_226]: (k1_xboole_0=B_224 | v1_partfun1(C_225, A_226) | ~v1_funct_2(C_225, A_226, B_224) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_226, B_224))) | ~v1_funct_1(C_225))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.45/3.87  tff(c_804, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_789])).
% 10.45/3.87  tff(c_830, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_xboole_0 | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_98, c_804])).
% 10.45/3.87  tff(c_924, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_830])).
% 10.45/3.87  tff(c_375, plain, (![D_180, C_181, B_182, A_183]: (m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(C_181, B_182))) | ~r1_tarski(k2_relat_1(D_180), B_182) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(C_181, A_183))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 10.45/3.87  tff(c_387, plain, (![B_182]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), B_182))) | ~r1_tarski(k2_relat_1('#skF_4'), B_182))), inference(resolution, [status(thm)], [c_99, c_375])).
% 10.45/3.87  tff(c_82, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_88, plain, (~v5_pre_topc('#skF_5', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_96, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_88])).
% 10.45/3.87  tff(c_287, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_96])).
% 10.45/3.87  tff(c_94, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_5', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_230])).
% 10.45/3.87  tff(c_95, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_94])).
% 10.45/3.87  tff(c_313, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_287, c_95])).
% 10.45/3.87  tff(c_1300, plain, (![D_283, A_284, B_285]: (v5_pre_topc(D_283, A_284, B_285) | ~v5_pre_topc(D_283, A_284, g1_pre_topc(u1_struct_0(B_285), u1_pre_topc(B_285))) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_284), u1_struct_0(g1_pre_topc(u1_struct_0(B_285), u1_pre_topc(B_285)))))) | ~v1_funct_2(D_283, u1_struct_0(A_284), u1_struct_0(g1_pre_topc(u1_struct_0(B_285), u1_pre_topc(B_285)))) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_284), u1_struct_0(B_285)))) | ~v1_funct_2(D_283, u1_struct_0(A_284), u1_struct_0(B_285)) | ~v1_funct_1(D_283) | ~l1_pre_topc(B_285) | ~v2_pre_topc(B_285) | ~l1_pre_topc(A_284) | ~v2_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_1327, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_99, c_1300])).
% 10.45/3.87  tff(c_1348, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_98, c_313, c_1327])).
% 10.45/3.87  tff(c_1365, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_1348])).
% 10.45/3.87  tff(c_1368, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1365])).
% 10.45/3.87  tff(c_1372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_1368])).
% 10.45/3.87  tff(c_1373, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_1348])).
% 10.45/3.87  tff(c_1414, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1373])).
% 10.45/3.87  tff(c_1434, plain, (~r1_tarski(k2_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_387, c_1414])).
% 10.45/3.87  tff(c_1437, plain, (~v5_relat_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1434])).
% 10.45/3.87  tff(c_1441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_177, c_1437])).
% 10.45/3.87  tff(c_1443, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_1373])).
% 10.45/3.87  tff(c_1459, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1443, c_40])).
% 10.45/3.87  tff(c_1488, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_924, c_1459])).
% 10.45/3.87  tff(c_58, plain, (![D_66, A_52, B_60]: (v5_pre_topc(D_66, A_52, B_60) | ~v5_pre_topc(D_66, g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52)), B_60) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52))), u1_struct_0(B_60)))) | ~v1_funct_2(D_66, u1_struct_0(g1_pre_topc(u1_struct_0(A_52), u1_pre_topc(A_52))), u1_struct_0(B_60)) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_52), u1_struct_0(B_60)))) | ~v1_funct_2(D_66, u1_struct_0(A_52), u1_struct_0(B_60)) | ~v1_funct_1(D_66) | ~l1_pre_topc(B_60) | ~v2_pre_topc(B_60) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_1446, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1443, c_58])).
% 10.45/3.87  tff(c_1475, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_1446])).
% 10.45/3.87  tff(c_1476, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_287, c_1475])).
% 10.45/3.87  tff(c_1497, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1476])).
% 10.45/3.87  tff(c_1509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1497])).
% 10.45/3.87  tff(c_1510, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_1476])).
% 10.45/3.87  tff(c_1442, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_1373])).
% 10.45/3.87  tff(c_1524, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_1442])).
% 10.45/3.87  tff(c_1525, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_1510, c_1524])).
% 10.45/3.87  tff(c_1528, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_217, c_1525])).
% 10.45/3.87  tff(c_1532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1528])).
% 10.45/3.87  tff(c_1533, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_830])).
% 10.45/3.87  tff(c_14, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.45/3.87  tff(c_254, plain, (![A_7]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~r2_hidden(A_7, '#skF_4'))), inference(resolution, [status(thm)], [c_99, c_14])).
% 10.45/3.87  tff(c_363, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(splitLeft, [status(thm)], [c_254])).
% 10.45/3.87  tff(c_1535, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1533, c_363])).
% 10.45/3.87  tff(c_1541, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6, c_1535])).
% 10.45/3.87  tff(c_1544, plain, (![A_302]: (~r2_hidden(A_302, '#skF_4'))), inference(splitRight, [status(thm)], [c_254])).
% 10.45/3.87  tff(c_1549, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_1544])).
% 10.45/3.87  tff(c_1572, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_2])).
% 10.45/3.87  tff(c_1571, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_1549, c_6])).
% 10.45/3.87  tff(c_10, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.45/3.87  tff(c_1569, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_10])).
% 10.45/3.87  tff(c_46, plain, (![B_46, C_47, A_45]: (k1_xboole_0=B_46 | v1_partfun1(C_47, A_45) | ~v1_funct_2(C_47, A_45, B_46) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))) | ~v1_funct_1(C_47))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.45/3.87  tff(c_1731, plain, (![B_324, C_325, A_326]: (B_324='#skF_4' | v1_partfun1(C_325, A_326) | ~v1_funct_2(C_325, A_326, B_324) | ~m1_subset_1(C_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_324))) | ~v1_funct_1(C_325))), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_46])).
% 10.45/3.87  tff(c_1741, plain, (![B_324, A_326]: (B_324='#skF_4' | v1_partfun1('#skF_4', A_326) | ~v1_funct_2('#skF_4', A_326, B_324) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1569, c_1731])).
% 10.45/3.87  tff(c_1778, plain, (![B_343, A_344]: (B_343='#skF_4' | v1_partfun1('#skF_4', A_344) | ~v1_funct_2('#skF_4', A_344, B_343))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1741])).
% 10.45/3.87  tff(c_1790, plain, (u1_struct_0('#skF_3')='#skF_4' | v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_1778])).
% 10.45/3.87  tff(c_1791, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1790])).
% 10.45/3.87  tff(c_1587, plain, (![A_306]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_306)))), inference(demodulation, [status(thm), theory('equality')], [c_1549, c_10])).
% 10.45/3.87  tff(c_1591, plain, (![A_42, B_43]: (v1_funct_2('#skF_4', A_42, B_43) | ~v1_partfun1('#skF_4', A_42) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1587, c_40])).
% 10.45/3.87  tff(c_1618, plain, (![A_42, B_43]: (v1_funct_2('#skF_4', A_42, B_43) | ~v1_partfun1('#skF_4', A_42))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1591])).
% 10.45/3.87  tff(c_1800, plain, (![D_353, A_354, B_355]: (v5_pre_topc(D_353, A_354, B_355) | ~v5_pre_topc(D_353, g1_pre_topc(u1_struct_0(A_354), u1_pre_topc(A_354)), B_355) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_354), u1_pre_topc(A_354))), u1_struct_0(B_355)))) | ~v1_funct_2(D_353, u1_struct_0(g1_pre_topc(u1_struct_0(A_354), u1_pre_topc(A_354))), u1_struct_0(B_355)) | ~m1_subset_1(D_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_354), u1_struct_0(B_355)))) | ~v1_funct_2(D_353, u1_struct_0(A_354), u1_struct_0(B_355)) | ~v1_funct_1(D_353) | ~l1_pre_topc(B_355) | ~v2_pre_topc(B_355) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_1804, plain, (![A_354, B_355]: (v5_pre_topc('#skF_4', A_354, B_355) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_354), u1_pre_topc(A_354)), B_355) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_354), u1_pre_topc(A_354))), u1_struct_0(B_355)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_354), u1_struct_0(B_355)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_354), u1_struct_0(B_355)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_355) | ~v2_pre_topc(B_355) | ~l1_pre_topc(A_354) | ~v2_pre_topc(A_354))), inference(resolution, [status(thm)], [c_1569, c_1800])).
% 10.45/3.87  tff(c_2046, plain, (![A_402, B_403]: (v5_pre_topc('#skF_4', A_402, B_403) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_402), u1_pre_topc(A_402)), B_403) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_402), u1_pre_topc(A_402))), u1_struct_0(B_403)) | ~v1_funct_2('#skF_4', u1_struct_0(A_402), u1_struct_0(B_403)) | ~l1_pre_topc(B_403) | ~v2_pre_topc(B_403) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1569, c_1804])).
% 10.45/3.87  tff(c_2052, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_98, c_2046])).
% 10.45/3.87  tff(c_2056, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_313, c_2052])).
% 10.45/3.87  tff(c_2065, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_2056])).
% 10.45/3.87  tff(c_2068, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_2065])).
% 10.45/3.87  tff(c_2072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2068])).
% 10.45/3.87  tff(c_2073, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_2056])).
% 10.45/3.87  tff(c_2108, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_2073])).
% 10.45/3.87  tff(c_2111, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1618, c_2108])).
% 10.45/3.87  tff(c_2115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1791, c_2111])).
% 10.45/3.87  tff(c_2116, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_2073])).
% 10.45/3.87  tff(c_2129, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_2116])).
% 10.45/3.87  tff(c_2132, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_217, c_2129])).
% 10.45/3.87  tff(c_2136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2132])).
% 10.45/3.87  tff(c_2137, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_2116])).
% 10.45/3.87  tff(c_2117, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitRight, [status(thm)], [c_2073])).
% 10.45/3.87  tff(c_1839, plain, (![D_365, A_366, B_367]: (v5_pre_topc(D_365, A_366, B_367) | ~v5_pre_topc(D_365, A_366, g1_pre_topc(u1_struct_0(B_367), u1_pre_topc(B_367))) | ~m1_subset_1(D_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366), u1_struct_0(g1_pre_topc(u1_struct_0(B_367), u1_pre_topc(B_367)))))) | ~v1_funct_2(D_365, u1_struct_0(A_366), u1_struct_0(g1_pre_topc(u1_struct_0(B_367), u1_pre_topc(B_367)))) | ~m1_subset_1(D_365, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366), u1_struct_0(B_367)))) | ~v1_funct_2(D_365, u1_struct_0(A_366), u1_struct_0(B_367)) | ~v1_funct_1(D_365) | ~l1_pre_topc(B_367) | ~v2_pre_topc(B_367) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_1843, plain, (![A_366, B_367]: (v5_pre_topc('#skF_4', A_366, B_367) | ~v5_pre_topc('#skF_4', A_366, g1_pre_topc(u1_struct_0(B_367), u1_pre_topc(B_367))) | ~v1_funct_2('#skF_4', u1_struct_0(A_366), u1_struct_0(g1_pre_topc(u1_struct_0(B_367), u1_pre_topc(B_367)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_366), u1_struct_0(B_367)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_366), u1_struct_0(B_367)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_367) | ~v2_pre_topc(B_367) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366))), inference(resolution, [status(thm)], [c_1569, c_1839])).
% 10.45/3.87  tff(c_2139, plain, (![A_420, B_421]: (v5_pre_topc('#skF_4', A_420, B_421) | ~v5_pre_topc('#skF_4', A_420, g1_pre_topc(u1_struct_0(B_421), u1_pre_topc(B_421))) | ~v1_funct_2('#skF_4', u1_struct_0(A_420), u1_struct_0(g1_pre_topc(u1_struct_0(B_421), u1_pre_topc(B_421)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_420), u1_struct_0(B_421)) | ~l1_pre_topc(B_421) | ~v2_pre_topc(B_421) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1569, c_1843])).
% 10.45/3.87  tff(c_2142, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2117, c_2139])).
% 10.45/3.87  tff(c_2151, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_76, c_2142])).
% 10.45/3.87  tff(c_2152, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_287, c_2151])).
% 10.45/3.87  tff(c_2158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2152])).
% 10.45/3.87  tff(c_2159, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1790])).
% 10.45/3.87  tff(c_193, plain, (![C_114, B_115, A_116]: (~v1_xboole_0(C_114) | ~m1_subset_1(B_115, k1_zfmisc_1(C_114)) | ~r2_hidden(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.45/3.87  tff(c_198, plain, (![A_116]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3'))) | ~r2_hidden(A_116, '#skF_4'))), inference(resolution, [status(thm)], [c_74, c_193])).
% 10.45/3.87  tff(c_200, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_198])).
% 10.45/3.87  tff(c_2163, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2159, c_200])).
% 10.45/3.87  tff(c_2168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1572, c_1571, c_2163])).
% 10.45/3.87  tff(c_2169, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_96])).
% 10.45/3.87  tff(c_2547, plain, (![D_515, A_516, B_517]: (v5_pre_topc(D_515, A_516, g1_pre_topc(u1_struct_0(B_517), u1_pre_topc(B_517))) | ~v5_pre_topc(D_515, A_516, B_517) | ~m1_subset_1(D_515, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_516), u1_struct_0(g1_pre_topc(u1_struct_0(B_517), u1_pre_topc(B_517)))))) | ~v1_funct_2(D_515, u1_struct_0(A_516), u1_struct_0(g1_pre_topc(u1_struct_0(B_517), u1_pre_topc(B_517)))) | ~m1_subset_1(D_515, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_516), u1_struct_0(B_517)))) | ~v1_funct_2(D_515, u1_struct_0(A_516), u1_struct_0(B_517)) | ~v1_funct_1(D_515) | ~l1_pre_topc(B_517) | ~v2_pre_topc(B_517) | ~l1_pre_topc(A_516) | ~v2_pre_topc(A_516))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_2558, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_99, c_2547])).
% 10.45/3.87  tff(c_2569, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_98, c_2558])).
% 10.45/3.87  tff(c_2570, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_2169, c_2569])).
% 10.45/3.87  tff(c_3103, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_2570])).
% 10.45/3.87  tff(c_3106, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_3103])).
% 10.45/3.87  tff(c_3110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_3106])).
% 10.45/3.87  tff(c_3111, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_2570])).
% 10.45/3.87  tff(c_3152, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_3111])).
% 10.45/3.87  tff(c_2170, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_96])).
% 10.45/3.87  tff(c_2719, plain, (![B_524]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), B_524))) | ~r1_tarski(k2_relat_1('#skF_4'), B_524))), inference(resolution, [status(thm)], [c_99, c_2296])).
% 10.45/3.87  tff(c_2733, plain, (![B_524]: (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), B_524) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_funct_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_524))), inference(resolution, [status(thm)], [c_2719, c_40])).
% 10.45/3.87  tff(c_2761, plain, (![B_524]: (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), B_524) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k2_relat_1('#skF_4'), B_524))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_2733])).
% 10.45/3.87  tff(c_3460, plain, (![B_611]: (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), B_611) | ~r1_tarski(k2_relat_1('#skF_4'), B_611))), inference(demodulation, [status(thm), theory('equality')], [c_2769, c_2761])).
% 10.45/3.87  tff(c_2372, plain, (![B_496]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_496, u1_struct_0('#skF_3')))) | ~r1_tarski(k1_relat_1('#skF_4'), B_496))), inference(resolution, [status(thm)], [c_74, c_2356])).
% 10.45/3.87  tff(c_2783, plain, (![D_531, A_532, B_533]: (v5_pre_topc(D_531, g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532)), B_533) | ~v5_pre_topc(D_531, A_532, B_533) | ~m1_subset_1(D_531, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532))), u1_struct_0(B_533)))) | ~v1_funct_2(D_531, u1_struct_0(g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532))), u1_struct_0(B_533)) | ~m1_subset_1(D_531, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532), u1_struct_0(B_533)))) | ~v1_funct_2(D_531, u1_struct_0(A_532), u1_struct_0(B_533)) | ~v1_funct_1(D_531) | ~l1_pre_topc(B_533) | ~v2_pre_topc(B_533) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_2807, plain, (![A_532]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532)), '#skF_3') | ~v5_pre_topc('#skF_4', A_532, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_532), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532)))))), inference(resolution, [status(thm)], [c_2372, c_2783])).
% 10.45/3.87  tff(c_2828, plain, (![A_532]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532)), '#skF_3') | ~v5_pre_topc('#skF_4', A_532, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_532), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_532), u1_struct_0('#skF_3')) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(A_532), u1_pre_topc(A_532)))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_2807])).
% 10.45/3.87  tff(c_3464, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k2_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3460, c_2828])).
% 10.45/3.87  tff(c_3477, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k2_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_76, c_74, c_2170, c_3464])).
% 10.45/3.87  tff(c_3478, plain, (~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~r1_tarski(k2_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_3152, c_3477])).
% 10.45/3.87  tff(c_3489, plain, (~r1_tarski(k2_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_3478])).
% 10.45/3.87  tff(c_3492, plain, (~v5_relat_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3489])).
% 10.45/3.87  tff(c_3496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_177, c_3492])).
% 10.45/3.87  tff(c_3497, plain, (~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitRight, [status(thm)], [c_3478])).
% 10.45/3.87  tff(c_3556, plain, (~v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_3497])).
% 10.45/3.87  tff(c_3560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_253, c_3556])).
% 10.45/3.87  tff(c_3561, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_3111])).
% 10.45/3.87  tff(c_3595, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_3561])).
% 10.45/3.87  tff(c_3598, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_217, c_3595])).
% 10.45/3.87  tff(c_3602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_3598])).
% 10.45/3.87  tff(c_3603, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(splitRight, [status(thm)], [c_3561])).
% 10.45/3.87  tff(c_3711, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))))), inference(splitLeft, [status(thm)], [c_3603])).
% 10.45/3.87  tff(c_3727, plain, (~r1_tarski(k2_relat_1('#skF_4'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_2308, c_3711])).
% 10.45/3.87  tff(c_3734, plain, (~v5_relat_1('#skF_4', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3727])).
% 10.45/3.87  tff(c_3738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_177, c_3734])).
% 10.45/3.87  tff(c_3739, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_3603])).
% 10.45/3.87  tff(c_3746, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v4_relat_1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v5_relat_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3065, c_3739])).
% 10.45/3.87  tff(c_3754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_253, c_2769, c_3746])).
% 10.45/3.87  tff(c_3755, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2473])).
% 10.45/3.87  tff(c_2252, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(splitLeft, [status(thm)], [c_254])).
% 10.45/3.87  tff(c_3786, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_3755, c_2252])).
% 10.45/3.87  tff(c_3794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6, c_3786])).
% 10.45/3.87  tff(c_3797, plain, (![A_628]: (~r2_hidden(A_628, '#skF_4'))), inference(splitRight, [status(thm)], [c_254])).
% 10.45/3.87  tff(c_3802, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_3797])).
% 10.45/3.87  tff(c_3822, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3802, c_2])).
% 10.45/3.87  tff(c_3821, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3802, c_3802, c_6])).
% 10.45/3.87  tff(c_3819, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_3802, c_10])).
% 10.45/3.87  tff(c_4001, plain, (![B_665, C_666, A_667]: (B_665='#skF_4' | v1_partfun1(C_666, A_667) | ~v1_funct_2(C_666, A_667, B_665) | ~m1_subset_1(C_666, k1_zfmisc_1(k2_zfmisc_1(A_667, B_665))) | ~v1_funct_1(C_666))), inference(demodulation, [status(thm), theory('equality')], [c_3802, c_46])).
% 10.45/3.87  tff(c_4008, plain, (![B_665, A_667]: (B_665='#skF_4' | v1_partfun1('#skF_4', A_667) | ~v1_funct_2('#skF_4', A_667, B_665) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3819, c_4001])).
% 10.45/3.87  tff(c_4016, plain, (![B_668, A_669]: (B_668='#skF_4' | v1_partfun1('#skF_4', A_669) | ~v1_funct_2('#skF_4', A_669, B_668))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4008])).
% 10.45/3.87  tff(c_4028, plain, (u1_struct_0('#skF_3')='#skF_4' | v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_4016])).
% 10.45/3.87  tff(c_4029, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_4028])).
% 10.45/3.87  tff(c_3913, plain, (![C_638, A_639, B_640]: (v1_funct_2(C_638, A_639, B_640) | ~v1_partfun1(C_638, A_639) | ~v1_funct_1(C_638) | ~m1_subset_1(C_638, k1_zfmisc_1(k2_zfmisc_1(A_639, B_640))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.45/3.87  tff(c_3920, plain, (![A_639, B_640]: (v1_funct_2('#skF_4', A_639, B_640) | ~v1_partfun1('#skF_4', A_639) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3819, c_3913])).
% 10.45/3.87  tff(c_3926, plain, (![A_639, B_640]: (v1_funct_2('#skF_4', A_639, B_640) | ~v1_partfun1('#skF_4', A_639))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3920])).
% 10.45/3.87  tff(c_4045, plain, (![D_680, A_681, B_682]: (v5_pre_topc(D_680, A_681, g1_pre_topc(u1_struct_0(B_682), u1_pre_topc(B_682))) | ~v5_pre_topc(D_680, A_681, B_682) | ~m1_subset_1(D_680, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_681), u1_struct_0(g1_pre_topc(u1_struct_0(B_682), u1_pre_topc(B_682)))))) | ~v1_funct_2(D_680, u1_struct_0(A_681), u1_struct_0(g1_pre_topc(u1_struct_0(B_682), u1_pre_topc(B_682)))) | ~m1_subset_1(D_680, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_681), u1_struct_0(B_682)))) | ~v1_funct_2(D_680, u1_struct_0(A_681), u1_struct_0(B_682)) | ~v1_funct_1(D_680) | ~l1_pre_topc(B_682) | ~v2_pre_topc(B_682) | ~l1_pre_topc(A_681) | ~v2_pre_topc(A_681))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_4049, plain, (![A_681, B_682]: (v5_pre_topc('#skF_4', A_681, g1_pre_topc(u1_struct_0(B_682), u1_pre_topc(B_682))) | ~v5_pre_topc('#skF_4', A_681, B_682) | ~v1_funct_2('#skF_4', u1_struct_0(A_681), u1_struct_0(g1_pre_topc(u1_struct_0(B_682), u1_pre_topc(B_682)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_681), u1_struct_0(B_682)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_681), u1_struct_0(B_682)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_682) | ~v2_pre_topc(B_682) | ~l1_pre_topc(A_681) | ~v2_pre_topc(A_681))), inference(resolution, [status(thm)], [c_3819, c_4045])).
% 10.45/3.87  tff(c_4378, plain, (![A_761, B_762]: (v5_pre_topc('#skF_4', A_761, g1_pre_topc(u1_struct_0(B_762), u1_pre_topc(B_762))) | ~v5_pre_topc('#skF_4', A_761, B_762) | ~v1_funct_2('#skF_4', u1_struct_0(A_761), u1_struct_0(g1_pre_topc(u1_struct_0(B_762), u1_pre_topc(B_762)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_761), u1_struct_0(B_762)) | ~l1_pre_topc(B_762) | ~v2_pre_topc(B_762) | ~l1_pre_topc(A_761) | ~v2_pre_topc(A_761))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3819, c_4049])).
% 10.45/3.87  tff(c_4385, plain, (![A_761, B_762]: (v5_pre_topc('#skF_4', A_761, g1_pre_topc(u1_struct_0(B_762), u1_pre_topc(B_762))) | ~v5_pre_topc('#skF_4', A_761, B_762) | ~v1_funct_2('#skF_4', u1_struct_0(A_761), u1_struct_0(B_762)) | ~l1_pre_topc(B_762) | ~v2_pre_topc(B_762) | ~l1_pre_topc(A_761) | ~v2_pre_topc(A_761) | ~v1_partfun1('#skF_4', u1_struct_0(A_761)))), inference(resolution, [status(thm)], [c_3926, c_4378])).
% 10.45/3.87  tff(c_4180, plain, (![D_702, A_703, B_704]: (v5_pre_topc(D_702, g1_pre_topc(u1_struct_0(A_703), u1_pre_topc(A_703)), B_704) | ~v5_pre_topc(D_702, A_703, B_704) | ~m1_subset_1(D_702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_703), u1_pre_topc(A_703))), u1_struct_0(B_704)))) | ~v1_funct_2(D_702, u1_struct_0(g1_pre_topc(u1_struct_0(A_703), u1_pre_topc(A_703))), u1_struct_0(B_704)) | ~m1_subset_1(D_702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703), u1_struct_0(B_704)))) | ~v1_funct_2(D_702, u1_struct_0(A_703), u1_struct_0(B_704)) | ~v1_funct_1(D_702) | ~l1_pre_topc(B_704) | ~v2_pre_topc(B_704) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_4192, plain, (![A_703, B_704]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_703), u1_pre_topc(A_703)), B_704) | ~v5_pre_topc('#skF_4', A_703, B_704) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_703), u1_pre_topc(A_703))), u1_struct_0(B_704)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_703), u1_struct_0(B_704)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_703), u1_struct_0(B_704)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_704) | ~v2_pre_topc(B_704) | ~l1_pre_topc(A_703) | ~v2_pre_topc(A_703))), inference(resolution, [status(thm)], [c_3819, c_4180])).
% 10.45/3.87  tff(c_4401, plain, (![A_765, B_766]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_765), u1_pre_topc(A_765)), B_766) | ~v5_pre_topc('#skF_4', A_765, B_766) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_765), u1_pre_topc(A_765))), u1_struct_0(B_766)) | ~v1_funct_2('#skF_4', u1_struct_0(A_765), u1_struct_0(B_766)) | ~l1_pre_topc(B_766) | ~v2_pre_topc(B_766) | ~l1_pre_topc(A_765) | ~v2_pre_topc(A_765))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_3819, c_4192])).
% 10.45/3.87  tff(c_4407, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_98, c_4401])).
% 10.45/3.87  tff(c_4411, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4407])).
% 10.45/3.87  tff(c_4412, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_2169, c_4411])).
% 10.45/3.87  tff(c_4423, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_4412])).
% 10.45/3.87  tff(c_4426, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_4423])).
% 10.45/3.87  tff(c_4430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_4426])).
% 10.45/3.87  tff(c_4431, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_4412])).
% 10.45/3.87  tff(c_4434, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_4431])).
% 10.45/3.87  tff(c_4448, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4385, c_4434])).
% 10.45/3.87  tff(c_4452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4029, c_86, c_84, c_82, c_80, c_76, c_2170, c_4448])).
% 10.45/3.87  tff(c_4453, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_4431])).
% 10.45/3.87  tff(c_4461, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_4453])).
% 10.45/3.87  tff(c_4467, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_217, c_4461])).
% 10.45/3.87  tff(c_4471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4467])).
% 10.45/3.87  tff(c_4472, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitRight, [status(thm)], [c_4453])).
% 10.45/3.87  tff(c_4476, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3926, c_4472])).
% 10.45/3.87  tff(c_4480, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4029, c_4476])).
% 10.45/3.87  tff(c_4481, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4028])).
% 10.45/3.87  tff(c_4485, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_2'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4481, c_200])).
% 10.45/3.87  tff(c_4490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3822, c_3821, c_4485])).
% 10.45/3.87  tff(c_4493, plain, (![A_769]: (~r2_hidden(A_769, '#skF_4'))), inference(splitRight, [status(thm)], [c_198])).
% 10.45/3.87  tff(c_4498, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_4493])).
% 10.45/3.87  tff(c_4507, plain, (![A_3]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_10])).
% 10.45/3.87  tff(c_9533, plain, (![B_1409, C_1410, A_1411]: (B_1409='#skF_4' | v1_partfun1(C_1410, A_1411) | ~v1_funct_2(C_1410, A_1411, B_1409) | ~m1_subset_1(C_1410, k1_zfmisc_1(k2_zfmisc_1(A_1411, B_1409))) | ~v1_funct_1(C_1410))), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_46])).
% 10.45/3.87  tff(c_9543, plain, (![B_1409, A_1411]: (B_1409='#skF_4' | v1_partfun1('#skF_4', A_1411) | ~v1_funct_2('#skF_4', A_1411, B_1409) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4507, c_9533])).
% 10.45/3.87  tff(c_9556, plain, (![B_1412, A_1413]: (B_1412='#skF_4' | v1_partfun1('#skF_4', A_1413) | ~v1_funct_2('#skF_4', A_1413, B_1412))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9543])).
% 10.45/3.87  tff(c_9568, plain, (u1_struct_0('#skF_3')='#skF_4' | v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_9556])).
% 10.45/3.87  tff(c_9569, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_9568])).
% 10.45/3.87  tff(c_4518, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_96])).
% 10.45/3.87  tff(c_4854, plain, (![B_866, C_867, A_868]: (B_866='#skF_4' | v1_partfun1(C_867, A_868) | ~v1_funct_2(C_867, A_868, B_866) | ~m1_subset_1(C_867, k1_zfmisc_1(k2_zfmisc_1(A_868, B_866))) | ~v1_funct_1(C_867))), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_46])).
% 10.45/3.87  tff(c_4867, plain, (![B_866, A_868]: (B_866='#skF_4' | v1_partfun1('#skF_4', A_868) | ~v1_funct_2('#skF_4', A_868, B_866) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4507, c_4854])).
% 10.45/3.87  tff(c_4877, plain, (![B_869, A_870]: (B_869='#skF_4' | v1_partfun1('#skF_4', A_870) | ~v1_funct_2('#skF_4', A_870, B_869))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4867])).
% 10.45/3.87  tff(c_4889, plain, (u1_struct_0('#skF_3')='#skF_4' | v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_4877])).
% 10.45/3.87  tff(c_4890, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_4889])).
% 10.45/3.87  tff(c_4691, plain, (![C_824, A_825, B_826]: (v1_funct_2(C_824, A_825, B_826) | ~v1_partfun1(C_824, A_825) | ~v1_funct_1(C_824) | ~m1_subset_1(C_824, k1_zfmisc_1(k2_zfmisc_1(A_825, B_826))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.45/3.87  tff(c_4698, plain, (![A_825, B_826]: (v1_funct_2('#skF_4', A_825, B_826) | ~v1_partfun1('#skF_4', A_825) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4507, c_4691])).
% 10.45/3.87  tff(c_4704, plain, (![A_825, B_826]: (v1_funct_2('#skF_4', A_825, B_826) | ~v1_partfun1('#skF_4', A_825))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4698])).
% 10.45/3.87  tff(c_4574, plain, (![A_777]: (m1_subset_1(u1_pre_topc(A_777), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_777)))) | ~l1_pre_topc(A_777))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.45/3.87  tff(c_4581, plain, (![A_777]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_777), u1_pre_topc(A_777))) | ~l1_pre_topc(A_777))), inference(resolution, [status(thm)], [c_4574, c_48])).
% 10.45/3.87  tff(c_4888, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_98, c_4877])).
% 10.45/3.87  tff(c_4891, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_4888])).
% 10.45/3.87  tff(c_4584, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_4518, c_95])).
% 10.45/3.87  tff(c_4999, plain, (![D_903, A_904, B_905]: (v5_pre_topc(D_903, A_904, B_905) | ~v5_pre_topc(D_903, A_904, g1_pre_topc(u1_struct_0(B_905), u1_pre_topc(B_905))) | ~m1_subset_1(D_903, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904), u1_struct_0(g1_pre_topc(u1_struct_0(B_905), u1_pre_topc(B_905)))))) | ~v1_funct_2(D_903, u1_struct_0(A_904), u1_struct_0(g1_pre_topc(u1_struct_0(B_905), u1_pre_topc(B_905)))) | ~m1_subset_1(D_903, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904), u1_struct_0(B_905)))) | ~v1_funct_2(D_903, u1_struct_0(A_904), u1_struct_0(B_905)) | ~v1_funct_1(D_903) | ~l1_pre_topc(B_905) | ~v2_pre_topc(B_905) | ~l1_pre_topc(A_904) | ~v2_pre_topc(A_904))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_5011, plain, (![A_904, B_905]: (v5_pre_topc('#skF_4', A_904, B_905) | ~v5_pre_topc('#skF_4', A_904, g1_pre_topc(u1_struct_0(B_905), u1_pre_topc(B_905))) | ~v1_funct_2('#skF_4', u1_struct_0(A_904), u1_struct_0(g1_pre_topc(u1_struct_0(B_905), u1_pre_topc(B_905)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_904), u1_struct_0(B_905)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_904), u1_struct_0(B_905)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_905) | ~v2_pre_topc(B_905) | ~l1_pre_topc(A_904) | ~v2_pre_topc(A_904))), inference(resolution, [status(thm)], [c_4507, c_4999])).
% 10.45/3.87  tff(c_5118, plain, (![A_930, B_931]: (v5_pre_topc('#skF_4', A_930, B_931) | ~v5_pre_topc('#skF_4', A_930, g1_pre_topc(u1_struct_0(B_931), u1_pre_topc(B_931))) | ~v1_funct_2('#skF_4', u1_struct_0(A_930), u1_struct_0(g1_pre_topc(u1_struct_0(B_931), u1_pre_topc(B_931)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_930), u1_struct_0(B_931)) | ~l1_pre_topc(B_931) | ~v2_pre_topc(B_931) | ~l1_pre_topc(A_930) | ~v2_pre_topc(A_930))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_5011])).
% 10.45/3.87  tff(c_5124, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_5118])).
% 10.45/3.87  tff(c_5128, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_4584, c_5124])).
% 10.45/3.87  tff(c_5147, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_5128])).
% 10.45/3.87  tff(c_5150, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_5147])).
% 10.45/3.87  tff(c_5154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_5150])).
% 10.45/3.87  tff(c_5155, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_5128])).
% 10.45/3.87  tff(c_5168, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_5155])).
% 10.45/3.87  tff(c_5171, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_4704, c_5168])).
% 10.45/3.87  tff(c_5175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4891, c_5171])).
% 10.45/3.87  tff(c_5177, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_5155])).
% 10.45/3.87  tff(c_5073, plain, (![D_919, A_920, B_921]: (v5_pre_topc(D_919, A_920, B_921) | ~v5_pre_topc(D_919, g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920)), B_921) | ~m1_subset_1(D_919, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920))), u1_struct_0(B_921)))) | ~v1_funct_2(D_919, u1_struct_0(g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920))), u1_struct_0(B_921)) | ~m1_subset_1(D_919, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_920), u1_struct_0(B_921)))) | ~v1_funct_2(D_919, u1_struct_0(A_920), u1_struct_0(B_921)) | ~v1_funct_1(D_919) | ~l1_pre_topc(B_921) | ~v2_pre_topc(B_921) | ~l1_pre_topc(A_920) | ~v2_pre_topc(A_920))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_5085, plain, (![A_920, B_921]: (v5_pre_topc('#skF_4', A_920, B_921) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920)), B_921) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920))), u1_struct_0(B_921)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_920), u1_struct_0(B_921)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_920), u1_struct_0(B_921)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_921) | ~v2_pre_topc(B_921) | ~l1_pre_topc(A_920) | ~v2_pre_topc(A_920))), inference(resolution, [status(thm)], [c_4507, c_5073])).
% 10.45/3.87  tff(c_5090, plain, (![A_920, B_921]: (v5_pre_topc('#skF_4', A_920, B_921) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920)), B_921) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_920), u1_pre_topc(A_920))), u1_struct_0(B_921)) | ~v1_funct_2('#skF_4', u1_struct_0(A_920), u1_struct_0(B_921)) | ~l1_pre_topc(B_921) | ~v2_pre_topc(B_921) | ~l1_pre_topc(A_920) | ~v2_pre_topc(A_920))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_5085])).
% 10.45/3.87  tff(c_5180, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_5177, c_5090])).
% 10.45/3.87  tff(c_5196, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_76, c_5180])).
% 10.45/3.87  tff(c_5197, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_4518, c_5196])).
% 10.45/3.87  tff(c_5176, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_5155])).
% 10.45/3.87  tff(c_5219, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_5197, c_5176])).
% 10.45/3.87  tff(c_5222, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4581, c_5219])).
% 10.45/3.87  tff(c_5226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_5222])).
% 10.45/3.87  tff(c_5227, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_4'), inference(splitRight, [status(thm)], [c_4888])).
% 10.45/3.87  tff(c_5250, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5227, c_4581])).
% 10.45/3.87  tff(c_5305, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_5250])).
% 10.45/3.87  tff(c_5308, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_4581, c_5305])).
% 10.45/3.87  tff(c_5312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_5308])).
% 10.45/3.87  tff(c_5314, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_5250])).
% 10.45/3.87  tff(c_4506, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | A_28='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_34])).
% 10.45/3.87  tff(c_52, plain, (![A_50]: (m1_subset_1(u1_pre_topc(A_50), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_50)))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.45/3.87  tff(c_5253, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5227, c_52])).
% 10.45/3.87  tff(c_5432, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5314, c_5253])).
% 10.45/3.87  tff(c_12, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.45/3.87  tff(c_5452, plain, (![A_962]: (m1_subset_1(A_962, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_962, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(resolution, [status(thm)], [c_5432, c_12])).
% 10.45/3.87  tff(c_5457, plain, (m1_subset_1('#skF_1'(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), k1_zfmisc_1('#skF_4')) | u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_4'), inference(resolution, [status(thm)], [c_4506, c_5452])).
% 10.45/3.87  tff(c_5466, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_4'), inference(splitLeft, [status(thm)], [c_5457])).
% 10.45/3.87  tff(c_5489, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_4')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5466, c_54])).
% 10.45/3.87  tff(c_5510, plain, (v2_pre_topc(g1_pre_topc('#skF_4', '#skF_4')) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5314, c_5227, c_5489])).
% 10.45/3.87  tff(c_5556, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_5510])).
% 10.45/3.87  tff(c_5559, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_5556])).
% 10.45/3.87  tff(c_5563, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_5559])).
% 10.45/3.87  tff(c_5565, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_5510])).
% 10.45/3.87  tff(c_5266, plain, (![D_936, A_937, B_938]: (v5_pre_topc(D_936, A_937, B_938) | ~v5_pre_topc(D_936, A_937, g1_pre_topc(u1_struct_0(B_938), u1_pre_topc(B_938))) | ~m1_subset_1(D_936, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_937), u1_struct_0(g1_pre_topc(u1_struct_0(B_938), u1_pre_topc(B_938)))))) | ~v1_funct_2(D_936, u1_struct_0(A_937), u1_struct_0(g1_pre_topc(u1_struct_0(B_938), u1_pre_topc(B_938)))) | ~m1_subset_1(D_936, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_937), u1_struct_0(B_938)))) | ~v1_funct_2(D_936, u1_struct_0(A_937), u1_struct_0(B_938)) | ~v1_funct_1(D_936) | ~l1_pre_topc(B_938) | ~v2_pre_topc(B_938) | ~l1_pre_topc(A_937) | ~v2_pre_topc(A_937))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_5287, plain, (![A_937, B_938]: (v5_pre_topc('#skF_4', A_937, B_938) | ~v5_pre_topc('#skF_4', A_937, g1_pre_topc(u1_struct_0(B_938), u1_pre_topc(B_938))) | ~v1_funct_2('#skF_4', u1_struct_0(A_937), u1_struct_0(g1_pre_topc(u1_struct_0(B_938), u1_pre_topc(B_938)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_937), u1_struct_0(B_938)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_937), u1_struct_0(B_938)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_938) | ~v2_pre_topc(B_938) | ~l1_pre_topc(A_937) | ~v2_pre_topc(A_937))), inference(resolution, [status(thm)], [c_4507, c_5266])).
% 10.45/3.87  tff(c_5771, plain, (![A_997, B_998]: (v5_pre_topc('#skF_4', A_997, B_998) | ~v5_pre_topc('#skF_4', A_997, g1_pre_topc(u1_struct_0(B_998), u1_pre_topc(B_998))) | ~v1_funct_2('#skF_4', u1_struct_0(A_997), u1_struct_0(g1_pre_topc(u1_struct_0(B_998), u1_pre_topc(B_998)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_997), u1_struct_0(B_998)) | ~l1_pre_topc(B_998) | ~v2_pre_topc(B_998) | ~l1_pre_topc(A_997) | ~v2_pre_topc(A_997))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_5287])).
% 10.45/3.87  tff(c_5821, plain, (![A_1000, B_1001]: (v5_pre_topc('#skF_4', A_1000, B_1001) | ~v5_pre_topc('#skF_4', A_1000, g1_pre_topc(u1_struct_0(B_1001), u1_pre_topc(B_1001))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1000), u1_struct_0(B_1001)) | ~l1_pre_topc(B_1001) | ~v2_pre_topc(B_1001) | ~l1_pre_topc(A_1000) | ~v2_pre_topc(A_1000) | ~v1_partfun1('#skF_4', u1_struct_0(A_1000)))), inference(resolution, [status(thm)], [c_4704, c_5771])).
% 10.45/3.87  tff(c_5837, plain, (![A_1000]: (v5_pre_topc('#skF_4', A_1000, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1000, g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1000), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_1000) | ~v2_pre_topc(A_1000) | ~v1_partfun1('#skF_4', u1_struct_0(A_1000)))), inference(superposition, [status(thm), theory('equality')], [c_5227, c_5821])).
% 10.45/3.87  tff(c_5870, plain, (![A_1002]: (v5_pre_topc('#skF_4', A_1002, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1002, g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(A_1002), '#skF_4') | ~l1_pre_topc(A_1002) | ~v2_pre_topc(A_1002) | ~v1_partfun1('#skF_4', u1_struct_0(A_1002)))), inference(demodulation, [status(thm), theory('equality')], [c_5565, c_5314, c_5227, c_5466, c_5837])).
% 10.45/3.87  tff(c_5783, plain, (![A_997]: (v5_pre_topc('#skF_4', A_997, '#skF_3') | ~v5_pre_topc('#skF_4', A_997, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_997), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_997), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_997) | ~v2_pre_topc(A_997))), inference(superposition, [status(thm), theory('equality')], [c_5227, c_5771])).
% 10.45/3.87  tff(c_5794, plain, (![A_997]: (v5_pre_topc('#skF_4', A_997, '#skF_3') | ~v5_pre_topc('#skF_4', A_997, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_997), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_997), u1_struct_0('#skF_3')) | ~l1_pre_topc(A_997) | ~v2_pre_topc(A_997))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_5783])).
% 10.45/3.87  tff(c_5943, plain, (![A_1006]: (v5_pre_topc('#skF_4', A_1006, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1006), u1_struct_0('#skF_3')) | ~v5_pre_topc('#skF_4', A_1006, g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(A_1006), '#skF_4') | ~l1_pre_topc(A_1006) | ~v2_pre_topc(A_1006) | ~v1_partfun1('#skF_4', u1_struct_0(A_1006)))), inference(resolution, [status(thm)], [c_5870, c_5794])).
% 10.45/3.87  tff(c_5952, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_76, c_5943])).
% 10.45/3.87  tff(c_5958, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4890, c_86, c_84, c_5952])).
% 10.45/3.87  tff(c_5959, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc('#skF_4', '#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_4518, c_5958])).
% 10.45/3.87  tff(c_5960, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_5959])).
% 10.45/3.87  tff(c_5963, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4704, c_5960])).
% 10.45/3.87  tff(c_5967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4890, c_5963])).
% 10.45/3.87  tff(c_5969, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_5959])).
% 10.45/3.87  tff(c_5229, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5227, c_98])).
% 10.45/3.87  tff(c_5398, plain, (![D_959, A_960, B_961]: (v5_pre_topc(D_959, A_960, B_961) | ~v5_pre_topc(D_959, g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960)), B_961) | ~m1_subset_1(D_959, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960))), u1_struct_0(B_961)))) | ~v1_funct_2(D_959, u1_struct_0(g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960))), u1_struct_0(B_961)) | ~m1_subset_1(D_959, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_960), u1_struct_0(B_961)))) | ~v1_funct_2(D_959, u1_struct_0(A_960), u1_struct_0(B_961)) | ~v1_funct_1(D_959) | ~l1_pre_topc(B_961) | ~v2_pre_topc(B_961) | ~l1_pre_topc(A_960) | ~v2_pre_topc(A_960))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_5419, plain, (![A_960, B_961]: (v5_pre_topc('#skF_4', A_960, B_961) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960)), B_961) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_960), u1_pre_topc(A_960))), u1_struct_0(B_961)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_960), u1_struct_0(B_961)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_960), u1_struct_0(B_961)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_961) | ~v2_pre_topc(B_961) | ~l1_pre_topc(A_960) | ~v2_pre_topc(A_960))), inference(resolution, [status(thm)], [c_4507, c_5398])).
% 10.45/3.87  tff(c_5618, plain, (![A_984, B_985]: (v5_pre_topc('#skF_4', A_984, B_985) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984)), B_985) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984))), u1_struct_0(B_985)) | ~v1_funct_2('#skF_4', u1_struct_0(A_984), u1_struct_0(B_985)) | ~l1_pre_topc(B_985) | ~v2_pre_topc(B_985) | ~l1_pre_topc(A_984) | ~v2_pre_topc(A_984))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_5419])).
% 10.45/3.87  tff(c_5630, plain, (![A_984]: (v5_pre_topc('#skF_4', A_984, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984)), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_984), u1_pre_topc(A_984))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_984), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_984) | ~v2_pre_topc(A_984))), inference(superposition, [status(thm), theory('equality')], [c_5227, c_5618])).
% 10.45/3.87  tff(c_6364, plain, (![A_1023]: (v5_pre_topc('#skF_4', A_1023, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1023), u1_pre_topc(A_1023)), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1023), u1_pre_topc(A_1023))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1023), '#skF_4') | ~l1_pre_topc(A_1023) | ~v2_pre_topc(A_1023))), inference(demodulation, [status(thm), theory('equality')], [c_5565, c_5314, c_5227, c_5630])).
% 10.45/3.87  tff(c_6396, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4584, c_6364])).
% 10.45/3.87  tff(c_6416, plain, (v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_5969, c_5229, c_6396])).
% 10.45/3.87  tff(c_5795, plain, (![A_997, B_998]: (v5_pre_topc('#skF_4', A_997, B_998) | ~v5_pre_topc('#skF_4', A_997, g1_pre_topc(u1_struct_0(B_998), u1_pre_topc(B_998))) | ~v1_funct_2('#skF_4', u1_struct_0(A_997), u1_struct_0(B_998)) | ~l1_pre_topc(B_998) | ~v2_pre_topc(B_998) | ~l1_pre_topc(A_997) | ~v2_pre_topc(A_997) | ~v1_partfun1('#skF_4', u1_struct_0(A_997)))), inference(resolution, [status(thm)], [c_4704, c_5771])).
% 10.45/3.87  tff(c_6422, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_6416, c_5795])).
% 10.45/3.87  tff(c_6435, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4890, c_86, c_84, c_82, c_80, c_76, c_6422])).
% 10.45/3.87  tff(c_6437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4518, c_6435])).
% 10.45/3.87  tff(c_6438, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_4889])).
% 10.45/3.87  tff(c_6443, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6438, c_76])).
% 10.45/3.87  tff(c_7919, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_6438, c_4888])).
% 10.45/3.87  tff(c_7920, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_7919])).
% 10.45/3.87  tff(c_4509, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4498, c_4498, c_6])).
% 10.45/3.87  tff(c_7934, plain, (![D_1168, A_1169, B_1170]: (v5_pre_topc(D_1168, A_1169, B_1170) | ~v5_pre_topc(D_1168, g1_pre_topc(u1_struct_0(A_1169), u1_pre_topc(A_1169)), B_1170) | ~m1_subset_1(D_1168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1169), u1_pre_topc(A_1169))), u1_struct_0(B_1170)))) | ~v1_funct_2(D_1168, u1_struct_0(g1_pre_topc(u1_struct_0(A_1169), u1_pre_topc(A_1169))), u1_struct_0(B_1170)) | ~m1_subset_1(D_1168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1169), u1_struct_0(B_1170)))) | ~v1_funct_2(D_1168, u1_struct_0(A_1169), u1_struct_0(B_1170)) | ~v1_funct_1(D_1168) | ~l1_pre_topc(B_1170) | ~v2_pre_topc(B_1170) | ~l1_pre_topc(A_1169) | ~v2_pre_topc(A_1169))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_7940, plain, (![D_1168, A_1169]: (v5_pre_topc(D_1168, A_1169, '#skF_3') | ~v5_pre_topc(D_1168, g1_pre_topc(u1_struct_0(A_1169), u1_pre_topc(A_1169)), '#skF_3') | ~m1_subset_1(D_1168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1169), u1_pre_topc(A_1169))), '#skF_4'))) | ~v1_funct_2(D_1168, u1_struct_0(g1_pre_topc(u1_struct_0(A_1169), u1_pre_topc(A_1169))), u1_struct_0('#skF_3')) | ~m1_subset_1(D_1168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1169), u1_struct_0('#skF_3')))) | ~v1_funct_2(D_1168, u1_struct_0(A_1169), u1_struct_0('#skF_3')) | ~v1_funct_1(D_1168) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1169) | ~v2_pre_topc(A_1169))), inference(superposition, [status(thm), theory('equality')], [c_6438, c_7934])).
% 10.45/3.87  tff(c_8024, plain, (![D_1183, A_1184]: (v5_pre_topc(D_1183, A_1184, '#skF_3') | ~v5_pre_topc(D_1183, g1_pre_topc(u1_struct_0(A_1184), u1_pre_topc(A_1184)), '#skF_3') | ~v1_funct_2(D_1183, u1_struct_0(g1_pre_topc(u1_struct_0(A_1184), u1_pre_topc(A_1184))), '#skF_4') | ~m1_subset_1(D_1183, k1_zfmisc_1('#skF_4')) | ~v1_funct_2(D_1183, u1_struct_0(A_1184), '#skF_4') | ~v1_funct_1(D_1183) | ~l1_pre_topc(A_1184) | ~v2_pre_topc(A_1184))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_6438, c_4509, c_6438, c_6438, c_4509, c_7940])).
% 10.45/3.87  tff(c_8031, plain, (![A_1184]: (v5_pre_topc('#skF_4', A_1184, '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1184), u1_pre_topc(A_1184)), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~v1_funct_2('#skF_4', u1_struct_0(A_1184), '#skF_4') | ~v1_funct_1('#skF_4') | ~l1_pre_topc(A_1184) | ~v2_pre_topc(A_1184) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1184), u1_pre_topc(A_1184)))))), inference(resolution, [status(thm)], [c_4704, c_8024])).
% 10.45/3.87  tff(c_8241, plain, (![A_1224]: (v5_pre_topc('#skF_4', A_1224, '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1224), u1_pre_topc(A_1224)), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1224), '#skF_4') | ~l1_pre_topc(A_1224) | ~v2_pre_topc(A_1224) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1224), u1_pre_topc(A_1224)))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_8031])).
% 10.45/3.87  tff(c_8244, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_7920, c_8241])).
% 10.45/3.87  tff(c_8250, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_6443, c_8244])).
% 10.45/3.87  tff(c_8251, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_4518, c_8250])).
% 10.45/3.87  tff(c_6440, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_6438, c_4584])).
% 10.45/3.87  tff(c_6442, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_6438, c_98])).
% 10.45/3.87  tff(c_7890, plain, (![D_1164, A_1165, B_1166]: (v5_pre_topc(D_1164, A_1165, B_1166) | ~v5_pre_topc(D_1164, A_1165, g1_pre_topc(u1_struct_0(B_1166), u1_pre_topc(B_1166))) | ~m1_subset_1(D_1164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165), u1_struct_0(g1_pre_topc(u1_struct_0(B_1166), u1_pre_topc(B_1166)))))) | ~v1_funct_2(D_1164, u1_struct_0(A_1165), u1_struct_0(g1_pre_topc(u1_struct_0(B_1166), u1_pre_topc(B_1166)))) | ~m1_subset_1(D_1164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165), u1_struct_0(B_1166)))) | ~v1_funct_2(D_1164, u1_struct_0(A_1165), u1_struct_0(B_1166)) | ~v1_funct_1(D_1164) | ~l1_pre_topc(B_1166) | ~v2_pre_topc(B_1166) | ~l1_pre_topc(A_1165) | ~v2_pre_topc(A_1165))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_7908, plain, (![A_1165, B_1166]: (v5_pre_topc('#skF_4', A_1165, B_1166) | ~v5_pre_topc('#skF_4', A_1165, g1_pre_topc(u1_struct_0(B_1166), u1_pre_topc(B_1166))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1165), u1_struct_0(g1_pre_topc(u1_struct_0(B_1166), u1_pre_topc(B_1166)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1165), u1_struct_0(B_1166)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1165), u1_struct_0(B_1166)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1166) | ~v2_pre_topc(B_1166) | ~l1_pre_topc(A_1165) | ~v2_pre_topc(A_1165))), inference(resolution, [status(thm)], [c_4507, c_7890])).
% 10.45/3.87  tff(c_8301, plain, (![A_1231, B_1232]: (v5_pre_topc('#skF_4', A_1231, B_1232) | ~v5_pre_topc('#skF_4', A_1231, g1_pre_topc(u1_struct_0(B_1232), u1_pre_topc(B_1232))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1231), u1_struct_0(g1_pre_topc(u1_struct_0(B_1232), u1_pre_topc(B_1232)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1231), u1_struct_0(B_1232)) | ~l1_pre_topc(B_1232) | ~v2_pre_topc(B_1232) | ~l1_pre_topc(A_1231) | ~v2_pre_topc(A_1231))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_7908])).
% 10.45/3.87  tff(c_8307, plain, (![A_1231]: (v5_pre_topc('#skF_4', A_1231, '#skF_3') | ~v5_pre_topc('#skF_4', A_1231, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1231), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1231), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1231) | ~v2_pre_topc(A_1231))), inference(superposition, [status(thm), theory('equality')], [c_6438, c_8301])).
% 10.45/3.87  tff(c_8316, plain, (![A_1233]: (v5_pre_topc('#skF_4', A_1233, '#skF_3') | ~v5_pre_topc('#skF_4', A_1233, g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1233), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1233), '#skF_4') | ~l1_pre_topc(A_1233) | ~v2_pre_topc(A_1233))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_6438, c_6438, c_8307])).
% 10.45/3.87  tff(c_8319, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_6442, c_8316])).
% 10.45/3.87  tff(c_8328, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6440, c_8319])).
% 10.45/3.87  tff(c_8329, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_8251, c_8328])).
% 10.45/3.87  tff(c_8333, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_8329])).
% 10.45/3.87  tff(c_8336, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_8333])).
% 10.45/3.87  tff(c_8340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_8336])).
% 10.45/3.87  tff(c_8341, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(splitRight, [status(thm)], [c_8329])).
% 10.45/3.87  tff(c_8353, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(splitLeft, [status(thm)], [c_8341])).
% 10.45/3.87  tff(c_8356, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_4704, c_8353])).
% 10.45/3.87  tff(c_8360, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7920, c_8356])).
% 10.45/3.87  tff(c_8361, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_8341])).
% 10.45/3.87  tff(c_8365, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4581, c_8361])).
% 10.45/3.87  tff(c_8369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_8365])).
% 10.45/3.87  tff(c_8370, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))='#skF_4'), inference(splitRight, [status(thm)], [c_7919])).
% 10.45/3.87  tff(c_8400, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8370, c_6442])).
% 10.45/3.87  tff(c_8684, plain, (![A_1251, B_1252]: (v5_pre_topc('#skF_4', A_1251, B_1252) | ~v5_pre_topc('#skF_4', A_1251, g1_pre_topc(u1_struct_0(B_1252), u1_pre_topc(B_1252))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1251), u1_struct_0(g1_pre_topc(u1_struct_0(B_1252), u1_pre_topc(B_1252)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1251), u1_struct_0(B_1252)) | ~l1_pre_topc(B_1252) | ~v2_pre_topc(B_1252) | ~l1_pre_topc(A_1251) | ~v2_pre_topc(A_1251))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_7908])).
% 10.45/3.87  tff(c_8699, plain, (![A_1251]: (v5_pre_topc('#skF_4', A_1251, '#skF_3') | ~v5_pre_topc('#skF_4', A_1251, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1251), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1251), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1251) | ~v2_pre_topc(A_1251))), inference(superposition, [status(thm), theory('equality')], [c_6438, c_8684])).
% 10.45/3.87  tff(c_8799, plain, (![A_1271]: (v5_pre_topc('#skF_4', A_1271, '#skF_3') | ~v5_pre_topc('#skF_4', A_1271, g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1271), '#skF_4') | ~l1_pre_topc(A_1271) | ~v2_pre_topc(A_1271))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_6438, c_8370, c_6438, c_8699])).
% 10.45/3.87  tff(c_8802, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_6440, c_8799])).
% 10.45/3.87  tff(c_8805, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_8400, c_8802])).
% 10.45/3.87  tff(c_8927, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_8805])).
% 10.45/3.87  tff(c_8930, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_8927])).
% 10.45/3.87  tff(c_8934, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_8930])).
% 10.45/3.87  tff(c_8935, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_8805])).
% 10.45/3.87  tff(c_8960, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_8935])).
% 10.45/3.87  tff(c_8963, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4581, c_8960])).
% 10.45/3.87  tff(c_8967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_8963])).
% 10.45/3.87  tff(c_8968, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_8935])).
% 10.45/3.87  tff(c_8372, plain, (![D_1235, A_1236, B_1237]: (v5_pre_topc(D_1235, A_1236, B_1237) | ~v5_pre_topc(D_1235, g1_pre_topc(u1_struct_0(A_1236), u1_pre_topc(A_1236)), B_1237) | ~m1_subset_1(D_1235, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1236), u1_pre_topc(A_1236))), u1_struct_0(B_1237)))) | ~v1_funct_2(D_1235, u1_struct_0(g1_pre_topc(u1_struct_0(A_1236), u1_pre_topc(A_1236))), u1_struct_0(B_1237)) | ~m1_subset_1(D_1235, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1236), u1_struct_0(B_1237)))) | ~v1_funct_2(D_1235, u1_struct_0(A_1236), u1_struct_0(B_1237)) | ~v1_funct_1(D_1235) | ~l1_pre_topc(B_1237) | ~v2_pre_topc(B_1237) | ~l1_pre_topc(A_1236) | ~v2_pre_topc(A_1236))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_8390, plain, (![A_1236, B_1237]: (v5_pre_topc('#skF_4', A_1236, B_1237) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1236), u1_pre_topc(A_1236)), B_1237) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1236), u1_pre_topc(A_1236))), u1_struct_0(B_1237)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1236), u1_struct_0(B_1237)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1236), u1_struct_0(B_1237)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1237) | ~v2_pre_topc(B_1237) | ~l1_pre_topc(A_1236) | ~v2_pre_topc(A_1236))), inference(resolution, [status(thm)], [c_4507, c_8372])).
% 10.45/3.87  tff(c_8569, plain, (![A_1245, B_1246]: (v5_pre_topc('#skF_4', A_1245, B_1246) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1245), u1_pre_topc(A_1245)), B_1246) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1245), u1_pre_topc(A_1245))), u1_struct_0(B_1246)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1245), u1_struct_0(B_1246)) | ~l1_pre_topc(B_1246) | ~v2_pre_topc(B_1246) | ~l1_pre_topc(A_1245) | ~v2_pre_topc(A_1245))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_8390])).
% 10.45/3.87  tff(c_8581, plain, (![A_1245]: (v5_pre_topc('#skF_4', A_1245, '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1245), u1_pre_topc(A_1245)), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1245), u1_pre_topc(A_1245))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1245), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1245) | ~v2_pre_topc(A_1245))), inference(superposition, [status(thm), theory('equality')], [c_6438, c_8569])).
% 10.45/3.87  tff(c_9136, plain, (![A_1307]: (v5_pre_topc('#skF_4', A_1307, '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1307), u1_pre_topc(A_1307)), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1307), u1_pre_topc(A_1307))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1307), '#skF_4') | ~l1_pre_topc(A_1307) | ~v2_pre_topc(A_1307))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_6438, c_8581])).
% 10.45/3.87  tff(c_9142, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8400, c_9136])).
% 10.45/3.87  tff(c_9156, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_6443, c_8968, c_9142])).
% 10.45/3.87  tff(c_9158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4518, c_9156])).
% 10.45/3.87  tff(c_9160, plain, (v5_pre_topc('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_96])).
% 10.45/3.87  tff(c_9360, plain, (![C_1369, A_1370, B_1371]: (v1_funct_2(C_1369, A_1370, B_1371) | ~v1_partfun1(C_1369, A_1370) | ~v1_funct_1(C_1369) | ~m1_subset_1(C_1369, k1_zfmisc_1(k2_zfmisc_1(A_1370, B_1371))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 10.45/3.87  tff(c_9364, plain, (![A_1370, B_1371]: (v1_funct_2('#skF_4', A_1370, B_1371) | ~v1_partfun1('#skF_4', A_1370) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4507, c_9360])).
% 10.45/3.87  tff(c_9373, plain, (![A_1370, B_1371]: (v1_funct_2('#skF_4', A_1370, B_1371) | ~v1_partfun1('#skF_4', A_1370))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_9364])).
% 10.45/3.87  tff(c_11053, plain, (![D_1544, A_1545, B_1546]: (v5_pre_topc(D_1544, A_1545, g1_pre_topc(u1_struct_0(B_1546), u1_pre_topc(B_1546))) | ~v5_pre_topc(D_1544, A_1545, B_1546) | ~m1_subset_1(D_1544, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1545), u1_struct_0(g1_pre_topc(u1_struct_0(B_1546), u1_pre_topc(B_1546)))))) | ~v1_funct_2(D_1544, u1_struct_0(A_1545), u1_struct_0(g1_pre_topc(u1_struct_0(B_1546), u1_pre_topc(B_1546)))) | ~m1_subset_1(D_1544, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1545), u1_struct_0(B_1546)))) | ~v1_funct_2(D_1544, u1_struct_0(A_1545), u1_struct_0(B_1546)) | ~v1_funct_1(D_1544) | ~l1_pre_topc(B_1546) | ~v2_pre_topc(B_1546) | ~l1_pre_topc(A_1545) | ~v2_pre_topc(A_1545))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_11074, plain, (![A_1545, B_1546]: (v5_pre_topc('#skF_4', A_1545, g1_pre_topc(u1_struct_0(B_1546), u1_pre_topc(B_1546))) | ~v5_pre_topc('#skF_4', A_1545, B_1546) | ~v1_funct_2('#skF_4', u1_struct_0(A_1545), u1_struct_0(g1_pre_topc(u1_struct_0(B_1546), u1_pre_topc(B_1546)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1545), u1_struct_0(B_1546)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1545), u1_struct_0(B_1546)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1546) | ~v2_pre_topc(B_1546) | ~l1_pre_topc(A_1545) | ~v2_pre_topc(A_1545))), inference(resolution, [status(thm)], [c_4507, c_11053])).
% 10.45/3.87  tff(c_11370, plain, (![A_1579, B_1580]: (v5_pre_topc('#skF_4', A_1579, g1_pre_topc(u1_struct_0(B_1580), u1_pre_topc(B_1580))) | ~v5_pre_topc('#skF_4', A_1579, B_1580) | ~v1_funct_2('#skF_4', u1_struct_0(A_1579), u1_struct_0(g1_pre_topc(u1_struct_0(B_1580), u1_pre_topc(B_1580)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1579), u1_struct_0(B_1580)) | ~l1_pre_topc(B_1580) | ~v2_pre_topc(B_1580) | ~l1_pre_topc(A_1579) | ~v2_pre_topc(A_1579))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_11074])).
% 10.45/3.87  tff(c_11389, plain, (![A_1579, B_1580]: (v5_pre_topc('#skF_4', A_1579, g1_pre_topc(u1_struct_0(B_1580), u1_pre_topc(B_1580))) | ~v5_pre_topc('#skF_4', A_1579, B_1580) | ~v1_funct_2('#skF_4', u1_struct_0(A_1579), u1_struct_0(B_1580)) | ~l1_pre_topc(B_1580) | ~v2_pre_topc(B_1580) | ~l1_pre_topc(A_1579) | ~v2_pre_topc(A_1579) | ~v1_partfun1('#skF_4', u1_struct_0(A_1579)))), inference(resolution, [status(thm)], [c_9373, c_11370])).
% 10.45/3.87  tff(c_9567, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_98, c_9556])).
% 10.45/3.87  tff(c_9570, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_9567])).
% 10.45/3.87  tff(c_9621, plain, (![D_1426, A_1427, B_1428]: (v5_pre_topc(D_1426, g1_pre_topc(u1_struct_0(A_1427), u1_pre_topc(A_1427)), B_1428) | ~v5_pre_topc(D_1426, A_1427, B_1428) | ~m1_subset_1(D_1426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1427), u1_pre_topc(A_1427))), u1_struct_0(B_1428)))) | ~v1_funct_2(D_1426, u1_struct_0(g1_pre_topc(u1_struct_0(A_1427), u1_pre_topc(A_1427))), u1_struct_0(B_1428)) | ~m1_subset_1(D_1426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1427), u1_struct_0(B_1428)))) | ~v1_funct_2(D_1426, u1_struct_0(A_1427), u1_struct_0(B_1428)) | ~v1_funct_1(D_1426) | ~l1_pre_topc(B_1428) | ~v2_pre_topc(B_1428) | ~l1_pre_topc(A_1427) | ~v2_pre_topc(A_1427))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_9633, plain, (![A_1427, B_1428]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1427), u1_pre_topc(A_1427)), B_1428) | ~v5_pre_topc('#skF_4', A_1427, B_1428) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1427), u1_pre_topc(A_1427))), u1_struct_0(B_1428)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1427), u1_struct_0(B_1428)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1427), u1_struct_0(B_1428)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1428) | ~v2_pre_topc(B_1428) | ~l1_pre_topc(A_1427) | ~v2_pre_topc(A_1427))), inference(resolution, [status(thm)], [c_4507, c_9621])).
% 10.45/3.87  tff(c_9711, plain, (![A_1450, B_1451]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1450), u1_pre_topc(A_1450)), B_1451) | ~v5_pre_topc('#skF_4', A_1450, B_1451) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1450), u1_pre_topc(A_1450))), u1_struct_0(B_1451)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1450), u1_struct_0(B_1451)) | ~l1_pre_topc(B_1451) | ~v2_pre_topc(B_1451) | ~l1_pre_topc(A_1450) | ~v2_pre_topc(A_1450))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_9633])).
% 10.45/3.87  tff(c_9734, plain, (![A_1452, B_1453]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1452), u1_pre_topc(A_1452)), B_1453) | ~v5_pre_topc('#skF_4', A_1452, B_1453) | ~v1_funct_2('#skF_4', u1_struct_0(A_1452), u1_struct_0(B_1453)) | ~l1_pre_topc(B_1453) | ~v2_pre_topc(B_1453) | ~l1_pre_topc(A_1452) | ~v2_pre_topc(A_1452) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1452), u1_pre_topc(A_1452)))))), inference(resolution, [status(thm)], [c_9373, c_9711])).
% 10.45/3.87  tff(c_9736, plain, (![B_1453]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_1453) | ~v5_pre_topc('#skF_4', '#skF_2', B_1453) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_1453)) | ~l1_pre_topc(B_1453) | ~v2_pre_topc(B_1453) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_9570, c_9734])).
% 10.45/3.87  tff(c_9739, plain, (![B_1453]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_1453) | ~v5_pre_topc('#skF_4', '#skF_2', B_1453) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(B_1453)) | ~l1_pre_topc(B_1453) | ~v2_pre_topc(B_1453))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_9736])).
% 10.45/3.87  tff(c_9159, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_96])).
% 10.45/3.87  tff(c_9661, plain, (![D_1441, A_1442, B_1443]: (v5_pre_topc(D_1441, A_1442, B_1443) | ~v5_pre_topc(D_1441, A_1442, g1_pre_topc(u1_struct_0(B_1443), u1_pre_topc(B_1443))) | ~m1_subset_1(D_1441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1442), u1_struct_0(g1_pre_topc(u1_struct_0(B_1443), u1_pre_topc(B_1443)))))) | ~v1_funct_2(D_1441, u1_struct_0(A_1442), u1_struct_0(g1_pre_topc(u1_struct_0(B_1443), u1_pre_topc(B_1443)))) | ~m1_subset_1(D_1441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1442), u1_struct_0(B_1443)))) | ~v1_funct_2(D_1441, u1_struct_0(A_1442), u1_struct_0(B_1443)) | ~v1_funct_1(D_1441) | ~l1_pre_topc(B_1443) | ~v2_pre_topc(B_1443) | ~l1_pre_topc(A_1442) | ~v2_pre_topc(A_1442))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_9673, plain, (![A_1442, B_1443]: (v5_pre_topc('#skF_4', A_1442, B_1443) | ~v5_pre_topc('#skF_4', A_1442, g1_pre_topc(u1_struct_0(B_1443), u1_pre_topc(B_1443))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1442), u1_struct_0(g1_pre_topc(u1_struct_0(B_1443), u1_pre_topc(B_1443)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1442), u1_struct_0(B_1443)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1442), u1_struct_0(B_1443)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1443) | ~v2_pre_topc(B_1443) | ~l1_pre_topc(A_1442) | ~v2_pre_topc(A_1442))), inference(resolution, [status(thm)], [c_4507, c_9661])).
% 10.45/3.87  tff(c_9765, plain, (![A_1458, B_1459]: (v5_pre_topc('#skF_4', A_1458, B_1459) | ~v5_pre_topc('#skF_4', A_1458, g1_pre_topc(u1_struct_0(B_1459), u1_pre_topc(B_1459))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1458), u1_struct_0(g1_pre_topc(u1_struct_0(B_1459), u1_pre_topc(B_1459)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1458), u1_struct_0(B_1459)) | ~l1_pre_topc(B_1459) | ~v2_pre_topc(B_1459) | ~l1_pre_topc(A_1458) | ~v2_pre_topc(A_1458))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_9673])).
% 10.45/3.87  tff(c_9776, plain, (![A_1460, B_1461]: (v5_pre_topc('#skF_4', A_1460, B_1461) | ~v5_pre_topc('#skF_4', A_1460, g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1460), u1_struct_0(B_1461)) | ~l1_pre_topc(B_1461) | ~v2_pre_topc(B_1461) | ~l1_pre_topc(A_1460) | ~v2_pre_topc(A_1460) | ~v1_partfun1('#skF_4', u1_struct_0(A_1460)))), inference(resolution, [status(thm)], [c_9373, c_9765])).
% 10.45/3.87  tff(c_9780, plain, (![B_1461]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_1461) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_1461)) | ~l1_pre_topc(B_1461) | ~v2_pre_topc(B_1461) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))))), inference(resolution, [status(thm)], [c_9739, c_9776])).
% 10.45/3.87  tff(c_9783, plain, (![B_1461]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), B_1461) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(B_1461)) | ~l1_pre_topc(B_1461) | ~v2_pre_topc(B_1461) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(B_1461), u1_pre_topc(B_1461))))), inference(demodulation, [status(thm), theory('equality')], [c_9570, c_9780])).
% 10.45/3.87  tff(c_9784, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_9783])).
% 10.45/3.87  tff(c_9787, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_9784])).
% 10.45/3.87  tff(c_9791, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_9787])).
% 10.45/3.87  tff(c_9793, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_9783])).
% 10.45/3.87  tff(c_9740, plain, (![D_1454, A_1455, B_1456]: (v5_pre_topc(D_1454, A_1455, g1_pre_topc(u1_struct_0(B_1456), u1_pre_topc(B_1456))) | ~v5_pre_topc(D_1454, A_1455, B_1456) | ~m1_subset_1(D_1454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1455), u1_struct_0(g1_pre_topc(u1_struct_0(B_1456), u1_pre_topc(B_1456)))))) | ~v1_funct_2(D_1454, u1_struct_0(A_1455), u1_struct_0(g1_pre_topc(u1_struct_0(B_1456), u1_pre_topc(B_1456)))) | ~m1_subset_1(D_1454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1455), u1_struct_0(B_1456)))) | ~v1_funct_2(D_1454, u1_struct_0(A_1455), u1_struct_0(B_1456)) | ~v1_funct_1(D_1454) | ~l1_pre_topc(B_1456) | ~v2_pre_topc(B_1456) | ~l1_pre_topc(A_1455) | ~v2_pre_topc(A_1455))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_9752, plain, (![A_1455, B_1456]: (v5_pre_topc('#skF_4', A_1455, g1_pre_topc(u1_struct_0(B_1456), u1_pre_topc(B_1456))) | ~v5_pre_topc('#skF_4', A_1455, B_1456) | ~v1_funct_2('#skF_4', u1_struct_0(A_1455), u1_struct_0(g1_pre_topc(u1_struct_0(B_1456), u1_pre_topc(B_1456)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1455), u1_struct_0(B_1456)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1455), u1_struct_0(B_1456)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1456) | ~v2_pre_topc(B_1456) | ~l1_pre_topc(A_1455) | ~v2_pre_topc(A_1455))), inference(resolution, [status(thm)], [c_4507, c_9740])).
% 10.45/3.87  tff(c_9794, plain, (![A_1462, B_1463]: (v5_pre_topc('#skF_4', A_1462, g1_pre_topc(u1_struct_0(B_1463), u1_pre_topc(B_1463))) | ~v5_pre_topc('#skF_4', A_1462, B_1463) | ~v1_funct_2('#skF_4', u1_struct_0(A_1462), u1_struct_0(g1_pre_topc(u1_struct_0(B_1463), u1_pre_topc(B_1463)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1462), u1_struct_0(B_1463)) | ~l1_pre_topc(B_1463) | ~v2_pre_topc(B_1463) | ~l1_pre_topc(A_1462) | ~v2_pre_topc(A_1462))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_9752])).
% 10.45/3.87  tff(c_9800, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_98, c_9794])).
% 10.45/3.87  tff(c_9804, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9793, c_82, c_80, c_9800])).
% 10.45/3.87  tff(c_9805, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_9159, c_9804])).
% 10.45/3.87  tff(c_9806, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_9805])).
% 10.45/3.87  tff(c_9809, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_9253, c_9806])).
% 10.45/3.87  tff(c_9813, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_9809])).
% 10.45/3.87  tff(c_9814, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3')) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_9805])).
% 10.45/3.87  tff(c_9828, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_9814])).
% 10.45/3.87  tff(c_9831, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_9739, c_9828])).
% 10.45/3.87  tff(c_9835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_9160, c_9831])).
% 10.45/3.87  tff(c_9836, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_9814])).
% 10.45/3.87  tff(c_9840, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_9373, c_9836])).
% 10.45/3.87  tff(c_9844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9570, c_9840])).
% 10.45/3.87  tff(c_9845, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_4'), inference(splitRight, [status(thm)], [c_9567])).
% 10.45/3.87  tff(c_9847, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9845, c_98])).
% 10.45/3.87  tff(c_9868, plain, (l1_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9845, c_9253])).
% 10.45/3.87  tff(c_9947, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_9868])).
% 10.45/3.87  tff(c_9950, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_9253, c_9947])).
% 10.45/3.87  tff(c_9954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_9950])).
% 10.45/3.87  tff(c_9956, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_9868])).
% 10.45/3.87  tff(c_9862, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9845, c_54])).
% 10.45/3.87  tff(c_11265, plain, (v2_pre_topc(g1_pre_topc('#skF_4', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9956, c_9862])).
% 10.45/3.87  tff(c_11266, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_11265])).
% 10.45/3.87  tff(c_11269, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_11266])).
% 10.45/3.87  tff(c_11273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11269])).
% 10.45/3.87  tff(c_11275, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_11265])).
% 10.45/3.87  tff(c_9957, plain, (![D_1478, A_1479, B_1480]: (v5_pre_topc(D_1478, g1_pre_topc(u1_struct_0(A_1479), u1_pre_topc(A_1479)), B_1480) | ~v5_pre_topc(D_1478, A_1479, B_1480) | ~m1_subset_1(D_1478, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1479), u1_pre_topc(A_1479))), u1_struct_0(B_1480)))) | ~v1_funct_2(D_1478, u1_struct_0(g1_pre_topc(u1_struct_0(A_1479), u1_pre_topc(A_1479))), u1_struct_0(B_1480)) | ~m1_subset_1(D_1478, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1479), u1_struct_0(B_1480)))) | ~v1_funct_2(D_1478, u1_struct_0(A_1479), u1_struct_0(B_1480)) | ~v1_funct_1(D_1478) | ~l1_pre_topc(B_1480) | ~v2_pre_topc(B_1480) | ~l1_pre_topc(A_1479) | ~v2_pre_topc(A_1479))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_9978, plain, (![A_1479, B_1480]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1479), u1_pre_topc(A_1479)), B_1480) | ~v5_pre_topc('#skF_4', A_1479, B_1480) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1479), u1_pre_topc(A_1479))), u1_struct_0(B_1480)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1479), u1_struct_0(B_1480)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1479), u1_struct_0(B_1480)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1480) | ~v2_pre_topc(B_1480) | ~l1_pre_topc(A_1479) | ~v2_pre_topc(A_1479))), inference(resolution, [status(thm)], [c_4507, c_9957])).
% 10.45/3.87  tff(c_11312, plain, (![A_1572, B_1573]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1572), u1_pre_topc(A_1572)), B_1573) | ~v5_pre_topc('#skF_4', A_1572, B_1573) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1572), u1_pre_topc(A_1572))), u1_struct_0(B_1573)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1572), u1_struct_0(B_1573)) | ~l1_pre_topc(B_1573) | ~v2_pre_topc(B_1573) | ~l1_pre_topc(A_1572) | ~v2_pre_topc(A_1572))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_9978])).
% 10.45/3.87  tff(c_11321, plain, (![A_1572]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1572), u1_pre_topc(A_1572)), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1572, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1572), u1_pre_topc(A_1572))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1572), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_1572) | ~v2_pre_topc(A_1572))), inference(superposition, [status(thm), theory('equality')], [c_9845, c_11312])).
% 10.45/3.87  tff(c_11543, plain, (![A_1593]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1593), u1_pre_topc(A_1593)), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1593, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1593), u1_pre_topc(A_1593))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1593), '#skF_4') | ~l1_pre_topc(A_1593) | ~v2_pre_topc(A_1593))), inference(demodulation, [status(thm), theory('equality')], [c_11275, c_9956, c_9845, c_11321])).
% 10.45/3.87  tff(c_11558, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_11543, c_9159])).
% 10.45/3.87  tff(c_11574, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_9847, c_11558])).
% 10.45/3.87  tff(c_11577, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_11574])).
% 10.45/3.87  tff(c_11580, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_9373, c_11577])).
% 10.45/3.87  tff(c_11584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9569, c_11580])).
% 10.45/3.87  tff(c_11585, plain, (~v5_pre_topc('#skF_4', '#skF_2', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_11574])).
% 10.45/3.87  tff(c_11607, plain, (~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_11389, c_11585])).
% 10.45/3.87  tff(c_11614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9569, c_86, c_84, c_82, c_80, c_76, c_9160, c_11607])).
% 10.45/3.87  tff(c_11615, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_9568])).
% 10.45/3.87  tff(c_13142, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))='#skF_4' | v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_11615, c_9567])).
% 10.45/3.87  tff(c_13143, plain, (v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(splitLeft, [status(thm)], [c_13142])).
% 10.45/3.87  tff(c_11617, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11615, c_9159])).
% 10.45/3.87  tff(c_11620, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11615, c_76])).
% 10.45/3.87  tff(c_13207, plain, (![D_1737, A_1738, B_1739]: (v5_pre_topc(D_1737, g1_pre_topc(u1_struct_0(A_1738), u1_pre_topc(A_1738)), B_1739) | ~v5_pre_topc(D_1737, A_1738, B_1739) | ~m1_subset_1(D_1737, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1738), u1_pre_topc(A_1738))), u1_struct_0(B_1739)))) | ~v1_funct_2(D_1737, u1_struct_0(g1_pre_topc(u1_struct_0(A_1738), u1_pre_topc(A_1738))), u1_struct_0(B_1739)) | ~m1_subset_1(D_1737, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1738), u1_struct_0(B_1739)))) | ~v1_funct_2(D_1737, u1_struct_0(A_1738), u1_struct_0(B_1739)) | ~v1_funct_1(D_1737) | ~l1_pre_topc(B_1739) | ~v2_pre_topc(B_1739) | ~l1_pre_topc(A_1738) | ~v2_pre_topc(A_1738))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_13225, plain, (![A_1738, B_1739]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1738), u1_pre_topc(A_1738)), B_1739) | ~v5_pre_topc('#skF_4', A_1738, B_1739) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1738), u1_pre_topc(A_1738))), u1_struct_0(B_1739)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1738), u1_struct_0(B_1739)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1738), u1_struct_0(B_1739)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1739) | ~v2_pre_topc(B_1739) | ~l1_pre_topc(A_1738) | ~v2_pre_topc(A_1738))), inference(resolution, [status(thm)], [c_4507, c_13207])).
% 10.45/3.87  tff(c_13407, plain, (![A_1777, B_1778]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1777), u1_pre_topc(A_1777)), B_1778) | ~v5_pre_topc('#skF_4', A_1777, B_1778) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1777), u1_pre_topc(A_1777))), u1_struct_0(B_1778)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1777), u1_struct_0(B_1778)) | ~l1_pre_topc(B_1778) | ~v2_pre_topc(B_1778) | ~l1_pre_topc(A_1777) | ~v2_pre_topc(A_1777))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_13225])).
% 10.45/3.87  tff(c_13416, plain, (![A_1777]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1777), u1_pre_topc(A_1777)), '#skF_3') | ~v5_pre_topc('#skF_4', A_1777, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1777), u1_pre_topc(A_1777))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1777), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1777) | ~v2_pre_topc(A_1777))), inference(superposition, [status(thm), theory('equality')], [c_11615, c_13407])).
% 10.45/3.87  tff(c_13466, plain, (![A_1782]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1782), u1_pre_topc(A_1782)), '#skF_3') | ~v5_pre_topc('#skF_4', A_1782, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1782), u1_pre_topc(A_1782))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1782), '#skF_4') | ~l1_pre_topc(A_1782) | ~v2_pre_topc(A_1782))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11615, c_13416])).
% 10.45/3.87  tff(c_13476, plain, (![A_1783]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1783), u1_pre_topc(A_1783)), '#skF_3') | ~v5_pre_topc('#skF_4', A_1783, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1783), '#skF_4') | ~l1_pre_topc(A_1783) | ~v2_pre_topc(A_1783) | ~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1783), u1_pre_topc(A_1783)))))), inference(resolution, [status(thm)], [c_9373, c_13466])).
% 10.45/3.87  tff(c_13479, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_13143, c_13476])).
% 10.45/3.87  tff(c_13485, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_11620, c_9160, c_13479])).
% 10.45/3.87  tff(c_11619, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_11615, c_98])).
% 10.45/3.87  tff(c_11672, plain, (![D_1594, A_1595, B_1596]: (v5_pre_topc(D_1594, A_1595, g1_pre_topc(u1_struct_0(B_1596), u1_pre_topc(B_1596))) | ~v5_pre_topc(D_1594, A_1595, B_1596) | ~m1_subset_1(D_1594, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1595), u1_struct_0(g1_pre_topc(u1_struct_0(B_1596), u1_pre_topc(B_1596)))))) | ~v1_funct_2(D_1594, u1_struct_0(A_1595), u1_struct_0(g1_pre_topc(u1_struct_0(B_1596), u1_pre_topc(B_1596)))) | ~m1_subset_1(D_1594, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1595), u1_struct_0(B_1596)))) | ~v1_funct_2(D_1594, u1_struct_0(A_1595), u1_struct_0(B_1596)) | ~v1_funct_1(D_1594) | ~l1_pre_topc(B_1596) | ~v2_pre_topc(B_1596) | ~l1_pre_topc(A_1595) | ~v2_pre_topc(A_1595))), inference(cnfTransformation, [status(thm)], [f_200])).
% 10.45/3.87  tff(c_11690, plain, (![A_1595, B_1596]: (v5_pre_topc('#skF_4', A_1595, g1_pre_topc(u1_struct_0(B_1596), u1_pre_topc(B_1596))) | ~v5_pre_topc('#skF_4', A_1595, B_1596) | ~v1_funct_2('#skF_4', u1_struct_0(A_1595), u1_struct_0(g1_pre_topc(u1_struct_0(B_1596), u1_pre_topc(B_1596)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1595), u1_struct_0(B_1596)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1595), u1_struct_0(B_1596)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1596) | ~v2_pre_topc(B_1596) | ~l1_pre_topc(A_1595) | ~v2_pre_topc(A_1595))), inference(resolution, [status(thm)], [c_4507, c_11672])).
% 10.45/3.87  tff(c_13498, plain, (![A_1786, B_1787]: (v5_pre_topc('#skF_4', A_1786, g1_pre_topc(u1_struct_0(B_1787), u1_pre_topc(B_1787))) | ~v5_pre_topc('#skF_4', A_1786, B_1787) | ~v1_funct_2('#skF_4', u1_struct_0(A_1786), u1_struct_0(g1_pre_topc(u1_struct_0(B_1787), u1_pre_topc(B_1787)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1786), u1_struct_0(B_1787)) | ~l1_pre_topc(B_1787) | ~v2_pre_topc(B_1787) | ~l1_pre_topc(A_1786) | ~v2_pre_topc(A_1786))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_11690])).
% 10.45/3.87  tff(c_13504, plain, (![A_1786]: (v5_pre_topc('#skF_4', A_1786, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1786, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1786), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1786), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1786) | ~v2_pre_topc(A_1786))), inference(superposition, [status(thm), theory('equality')], [c_11615, c_13498])).
% 10.45/3.87  tff(c_13534, plain, (![A_1789]: (v5_pre_topc('#skF_4', A_1789, g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1789, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1789), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1789), '#skF_4') | ~l1_pre_topc(A_1789) | ~v2_pre_topc(A_1789))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11615, c_11615, c_13504])).
% 10.45/3.87  tff(c_13537, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_11619, c_13534])).
% 10.45/3.87  tff(c_13546, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13485, c_13537])).
% 10.45/3.87  tff(c_13547, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_11617, c_13546])).
% 10.45/3.87  tff(c_13551, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_13547])).
% 10.45/3.87  tff(c_13564, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_13551])).
% 10.45/3.87  tff(c_13568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_13564])).
% 10.45/3.87  tff(c_13569, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(splitRight, [status(thm)], [c_13547])).
% 10.45/3.87  tff(c_13571, plain, (~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(splitLeft, [status(thm)], [c_13569])).
% 10.45/3.87  tff(c_13574, plain, (~v1_partfun1('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))))), inference(resolution, [status(thm)], [c_9373, c_13571])).
% 10.45/3.87  tff(c_13578, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13143, c_13574])).
% 10.45/3.87  tff(c_13579, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_13569])).
% 10.45/3.87  tff(c_13583, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_9253, c_13579])).
% 10.45/3.87  tff(c_13587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_13583])).
% 10.45/3.87  tff(c_13588, plain, (u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))='#skF_4'), inference(splitRight, [status(thm)], [c_13142])).
% 10.45/3.87  tff(c_13618, plain, (v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13588, c_11619])).
% 10.45/3.87  tff(c_13999, plain, (![A_1828, B_1829]: (v5_pre_topc('#skF_4', A_1828, g1_pre_topc(u1_struct_0(B_1829), u1_pre_topc(B_1829))) | ~v5_pre_topc('#skF_4', A_1828, B_1829) | ~v1_funct_2('#skF_4', u1_struct_0(A_1828), u1_struct_0(g1_pre_topc(u1_struct_0(B_1829), u1_pre_topc(B_1829)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1828), u1_struct_0(B_1829)) | ~l1_pre_topc(B_1829) | ~v2_pre_topc(B_1829) | ~l1_pre_topc(A_1828) | ~v2_pre_topc(A_1828))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_11690])).
% 10.45/3.87  tff(c_14014, plain, (![A_1828]: (v5_pre_topc('#skF_4', A_1828, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1828, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1828), u1_struct_0(g1_pre_topc('#skF_4', u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1828), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1828) | ~v2_pre_topc(A_1828))), inference(superposition, [status(thm), theory('equality')], [c_11615, c_13999])).
% 10.45/3.87  tff(c_14081, plain, (![A_1840]: (v5_pre_topc('#skF_4', A_1840, g1_pre_topc('#skF_4', u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_4', A_1840, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(A_1840), '#skF_4') | ~l1_pre_topc(A_1840) | ~v2_pre_topc(A_1840))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11615, c_13588, c_11615, c_14014])).
% 10.45/3.87  tff(c_14088, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_14081, c_11617])).
% 10.45/3.87  tff(c_14094, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_13618, c_14088])).
% 10.45/3.87  tff(c_14135, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_14094])).
% 10.45/3.87  tff(c_14138, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_14135])).
% 10.45/3.87  tff(c_14142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_14138])).
% 10.45/3.87  tff(c_14143, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_14094])).
% 10.45/3.87  tff(c_14167, plain, (~v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_14143])).
% 10.45/3.87  tff(c_13698, plain, (![D_1794, A_1795, B_1796]: (v5_pre_topc(D_1794, g1_pre_topc(u1_struct_0(A_1795), u1_pre_topc(A_1795)), B_1796) | ~v5_pre_topc(D_1794, A_1795, B_1796) | ~m1_subset_1(D_1794, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1795), u1_pre_topc(A_1795))), u1_struct_0(B_1796)))) | ~v1_funct_2(D_1794, u1_struct_0(g1_pre_topc(u1_struct_0(A_1795), u1_pre_topc(A_1795))), u1_struct_0(B_1796)) | ~m1_subset_1(D_1794, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1795), u1_struct_0(B_1796)))) | ~v1_funct_2(D_1794, u1_struct_0(A_1795), u1_struct_0(B_1796)) | ~v1_funct_1(D_1794) | ~l1_pre_topc(B_1796) | ~v2_pre_topc(B_1796) | ~l1_pre_topc(A_1795) | ~v2_pre_topc(A_1795))), inference(cnfTransformation, [status(thm)], [f_171])).
% 10.45/3.87  tff(c_13722, plain, (![A_1795, B_1796]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1795), u1_pre_topc(A_1795)), B_1796) | ~v5_pre_topc('#skF_4', A_1795, B_1796) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1795), u1_pre_topc(A_1795))), u1_struct_0(B_1796)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1795), u1_struct_0(B_1796)))) | ~v1_funct_2('#skF_4', u1_struct_0(A_1795), u1_struct_0(B_1796)) | ~v1_funct_1('#skF_4') | ~l1_pre_topc(B_1796) | ~v2_pre_topc(B_1796) | ~l1_pre_topc(A_1795) | ~v2_pre_topc(A_1795))), inference(resolution, [status(thm)], [c_4507, c_13698])).
% 10.45/3.87  tff(c_13837, plain, (![A_1812, B_1813]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1812), u1_pre_topc(A_1812)), B_1813) | ~v5_pre_topc('#skF_4', A_1812, B_1813) | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1812), u1_pre_topc(A_1812))), u1_struct_0(B_1813)) | ~v1_funct_2('#skF_4', u1_struct_0(A_1812), u1_struct_0(B_1813)) | ~l1_pre_topc(B_1813) | ~v2_pre_topc(B_1813) | ~l1_pre_topc(A_1812) | ~v2_pre_topc(A_1812))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4507, c_13722])).
% 10.45/3.87  tff(c_13849, plain, (![A_1812]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1812), u1_pre_topc(A_1812)), '#skF_3') | ~v5_pre_topc('#skF_4', A_1812, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1812), u1_pre_topc(A_1812))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1812), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(A_1812) | ~v2_pre_topc(A_1812))), inference(superposition, [status(thm), theory('equality')], [c_11615, c_13837])).
% 10.45/3.87  tff(c_14283, plain, (![A_1853]: (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0(A_1853), u1_pre_topc(A_1853)), '#skF_3') | ~v5_pre_topc('#skF_4', A_1853, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0(g1_pre_topc(u1_struct_0(A_1853), u1_pre_topc(A_1853))), '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0(A_1853), '#skF_4') | ~l1_pre_topc(A_1853) | ~v2_pre_topc(A_1853))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_11615, c_13849])).
% 10.45/3.87  tff(c_14289, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3') | ~v5_pre_topc('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_13618, c_14283])).
% 10.45/3.87  tff(c_14303, plain, (v5_pre_topc('#skF_4', g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_11620, c_9160, c_14289])).
% 10.45/3.87  tff(c_14305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14167, c_14303])).
% 10.45/3.87  tff(c_14306, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_14143])).
% 10.45/3.87  tff(c_14310, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_9253, c_14306])).
% 10.45/3.87  tff(c_14314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_14310])).
% 10.45/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.45/3.87  
% 10.45/3.87  Inference rules
% 10.45/3.87  ----------------------
% 10.45/3.87  #Ref     : 0
% 10.45/3.87  #Sup     : 2601
% 10.45/3.87  #Fact    : 0
% 10.45/3.87  #Define  : 0
% 10.45/3.87  #Split   : 155
% 10.45/3.87  #Chain   : 0
% 10.45/3.87  #Close   : 0
% 10.45/3.87  
% 10.45/3.87  Ordering : KBO
% 10.45/3.87  
% 10.45/3.87  Simplification rules
% 10.45/3.87  ----------------------
% 10.45/3.87  #Subsume      : 827
% 10.45/3.87  #Demod        : 5550
% 10.45/3.87  #Tautology    : 719
% 10.45/3.87  #SimpNegUnit  : 128
% 10.45/3.87  #BackRed      : 199
% 10.45/3.87  
% 10.45/3.87  #Partial instantiations: 0
% 10.45/3.87  #Strategies tried      : 1
% 10.45/3.87  
% 10.45/3.87  Timing (in seconds)
% 10.45/3.87  ----------------------
% 10.45/3.87  Preprocessing        : 0.38
% 10.45/3.87  Parsing              : 0.20
% 10.45/3.87  CNF conversion       : 0.03
% 10.45/3.87  Main loop            : 2.56
% 10.45/3.87  Inferencing          : 0.85
% 10.45/3.87  Reduction            : 0.98
% 10.45/3.87  Demodulation         : 0.72
% 10.45/3.87  BG Simplification    : 0.07
% 10.45/3.87  Subsumption          : 0.48
% 10.45/3.87  Abstraction          : 0.09
% 10.45/3.87  MUC search           : 0.00
% 10.45/3.87  Cooper               : 0.00
% 10.45/3.87  Total                : 3.14
% 10.45/3.87  Index Insertion      : 0.00
% 10.45/3.87  Index Deletion       : 0.00
% 10.45/3.87  Index Matching       : 0.00
% 10.45/3.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
