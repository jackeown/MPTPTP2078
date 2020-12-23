%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:12 EST 2020

% Result     : Theorem 21.60s
% Output     : CNFRefutation 22.41s
% Verified   : 
% Statistics : Number of formulae       :  674 (46032 expanded)
%              Number of leaves         :   53 (14912 expanded)
%              Depth                    :   26
%              Number of atoms          : 1869 (149113 expanded)
%              Number of equality atoms :  187 (24610 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_mcart_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_251,negated_conjecture,(
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

tff(f_155,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_151,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_91,axiom,(
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

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_145,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_221,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_192,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_126,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_106,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_74,plain,(
    ! [A_53] :
      ( m1_subset_1(u1_pre_topc(A_53),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53))))
      | ~ l1_pre_topc(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_34163,plain,(
    ! [A_2495,B_2496] :
      ( l1_pre_topc(g1_pre_topc(A_2495,B_2496))
      | ~ m1_subset_1(B_2496,k1_zfmisc_1(k1_zfmisc_1(A_2495))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_34171,plain,(
    ! [A_53] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_74,c_34163])).

tff(c_108,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_88,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_110,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_120,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_110])).

tff(c_272,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_450,plain,(
    ! [A_152] :
      ( m1_subset_1(u1_pre_topc(A_152),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_152))))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_70,plain,(
    ! [A_51,B_52] :
      ( l1_pre_topc(g1_pre_topc(A_51,B_52))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_456,plain,(
    ! [A_152] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_152),u1_pre_topc(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_450,c_70])).

tff(c_76,plain,(
    ! [A_54] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_54),u1_pre_topc(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_104,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_102,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_98,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_117,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_98])).

tff(c_94,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_34,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_121,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_96])).

tff(c_212,plain,(
    ! [C_123,A_124,B_125] :
      ( v1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_235,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_121,c_212])).

tff(c_471,plain,(
    ! [C_156,A_157,B_158] :
      ( v4_relat_1(C_156,A_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_496,plain,(
    v4_relat_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_121,c_471])).

tff(c_637,plain,(
    ! [B_201,A_202] :
      ( k1_relat_1(B_201) = A_202
      | ~ v1_partfun1(B_201,A_202)
      | ~ v4_relat_1(B_201,A_202)
      | ~ v1_relat_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_646,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_496,c_637])).

tff(c_661,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_646])).

tff(c_703,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_661])).

tff(c_971,plain,(
    ! [B_243,C_244,A_245] :
      ( k1_xboole_0 = B_243
      | v1_partfun1(C_244,A_245)
      | ~ v1_funct_2(C_244,A_245,B_243)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_245,B_243)))
      | ~ v1_funct_1(C_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_980,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_121,c_971])).

tff(c_1003,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_117,c_980])).

tff(c_1004,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_703,c_1003])).

tff(c_239,plain,(
    ! [C_126,B_127,A_128] :
      ( ~ v1_xboole_0(C_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(C_126))
      | ~ r2_hidden(A_128,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_263,plain,(
    ! [A_128] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))
      | ~ r2_hidden(A_128,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_121,c_239])).

tff(c_531,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_1018,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1004,c_531])).

tff(c_1029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_1018])).

tff(c_1030,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_661])).

tff(c_92,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_1042,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_92])).

tff(c_90,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_1041,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_90])).

tff(c_1436,plain,(
    ! [B_276,C_277,A_278] :
      ( k1_xboole_0 = B_276
      | v1_partfun1(C_277,A_278)
      | ~ v1_funct_2(C_277,A_278,B_276)
      | ~ m1_subset_1(C_277,k1_zfmisc_1(k2_zfmisc_1(A_278,B_276)))
      | ~ v1_funct_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1445,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1041,c_1436])).

tff(c_1471,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1042,c_1445])).

tff(c_2176,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_1471])).

tff(c_498,plain,(
    v4_relat_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_90,c_471])).

tff(c_640,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_498,c_637])).

tff(c_655,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_640])).

tff(c_2302,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2176,c_1030,c_1030,c_655])).

tff(c_1040,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_117])).

tff(c_1039,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_121])).

tff(c_1048,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_76])).

tff(c_1063,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_1048])).

tff(c_1054,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_456])).

tff(c_1067,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_1054])).

tff(c_116,plain,
    ( v5_pre_topc('#skF_5','#skF_3','#skF_4')
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_118,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_116])).

tff(c_433,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_118])).

tff(c_1038,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_433])).

tff(c_1812,plain,(
    ! [D_322,A_323,B_324] :
      ( v5_pre_topc(D_322,A_323,B_324)
      | ~ v5_pre_topc(D_322,A_323,g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324)))
      | ~ m1_subset_1(D_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_323),u1_struct_0(g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324))))))
      | ~ v1_funct_2(D_322,u1_struct_0(A_323),u1_struct_0(g1_pre_topc(u1_struct_0(B_324),u1_pre_topc(B_324))))
      | ~ m1_subset_1(D_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_323),u1_struct_0(B_324))))
      | ~ v1_funct_2(D_322,u1_struct_0(A_323),u1_struct_0(B_324))
      | ~ v1_funct_1(D_322)
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | ~ l1_pre_topc(A_323)
      | ~ v2_pre_topc(A_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_1823,plain,
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
    inference(resolution,[status(thm)],[c_1041,c_1812])).

tff(c_1848,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1067,c_104,c_102,c_94,c_1042,c_1038,c_1823])).

tff(c_2801,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_2302,c_1039,c_2302,c_1848])).

tff(c_1245,plain,(
    ! [D_258,B_259,C_260,A_261] :
      ( m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(B_259,C_260)))
      | ~ r1_tarski(k1_relat_1(D_258),B_259)
      | ~ m1_subset_1(D_258,k1_zfmisc_1(k2_zfmisc_1(A_261,C_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1262,plain,(
    ! [B_259] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_259,u1_struct_0('#skF_4'))))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_259) ) ),
    inference(resolution,[status(thm)],[c_1039,c_1245])).

tff(c_2037,plain,(
    ! [D_345,A_346,B_347] :
      ( v5_pre_topc(D_345,A_346,B_347)
      | ~ v5_pre_topc(D_345,g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346)),B_347)
      | ~ m1_subset_1(D_345,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346))),u1_struct_0(B_347))))
      | ~ v1_funct_2(D_345,u1_struct_0(g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346))),u1_struct_0(B_347))
      | ~ m1_subset_1(D_345,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_346),u1_struct_0(B_347))))
      | ~ v1_funct_2(D_345,u1_struct_0(A_346),u1_struct_0(B_347))
      | ~ v1_funct_1(D_345)
      | ~ l1_pre_topc(B_347)
      | ~ v2_pre_topc(B_347)
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2049,plain,(
    ! [A_346] :
      ( v5_pre_topc('#skF_6',A_346,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346)),'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346))),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_346),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_346),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_346)
      | ~ v2_pre_topc(A_346)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_346),u1_pre_topc(A_346)))) ) ),
    inference(resolution,[status(thm)],[c_1262,c_2037])).

tff(c_4274,plain,(
    ! [A_530] :
      ( v5_pre_topc('#skF_6',A_530,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_530),u1_pre_topc(A_530)),'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_530),u1_pre_topc(A_530))),u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_530),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc(A_530)
      | ~ v2_pre_topc(A_530)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_530),u1_pre_topc(A_530)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_94,c_2049])).

tff(c_4286,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1030,c_4274])).

tff(c_4293,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2302,c_1030,c_108,c_106,c_1040,c_1030,c_1039,c_1030,c_1040,c_2302,c_2801,c_1030,c_4286])).

tff(c_4295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_4293])).

tff(c_4296,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1471])).

tff(c_268,plain,(
    ! [A_128] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
      | ~ r2_hidden(A_128,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_90,c_239])).

tff(c_470,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_1032,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_470])).

tff(c_4298,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4296,c_1032])).

tff(c_4306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_4298])).

tff(c_4309,plain,(
    ! [A_531] : ~ r2_hidden(A_531,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_4314,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_4309])).

tff(c_4336,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_2])).

tff(c_4335,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_4314,c_12])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4332,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_6',B_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_4314,c_14])).

tff(c_175,plain,(
    ! [A_114] : m1_subset_1(k6_partfun1(A_114),k1_zfmisc_1(k2_zfmisc_1(A_114,A_114))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_179,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_175])).

tff(c_249,plain,(
    ! [A_128] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_128,k6_partfun1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_179,c_239])).

tff(c_273,plain,(
    ! [A_130] : ~ r2_hidden(A_130,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_278,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_273])).

tff(c_4328,plain,(
    k6_partfun1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_4314,c_278])).

tff(c_50,plain,(
    ! [A_43] : m1_subset_1(k6_partfun1(A_43),k1_zfmisc_1(k2_zfmisc_1(A_43,A_43))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_236,plain,(
    ! [A_43] : v1_relat_1(k6_partfun1(A_43)) ),
    inference(resolution,[status(thm)],[c_50,c_212])).

tff(c_48,plain,(
    ! [A_43] : v1_partfun1(k6_partfun1(A_43),A_43) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_497,plain,(
    ! [A_43] : v4_relat_1(k6_partfun1(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_50,c_471])).

tff(c_4597,plain,(
    ! [B_550,A_551] :
      ( k1_relat_1(B_550) = A_551
      | ~ v1_partfun1(B_550,A_551)
      | ~ v4_relat_1(B_550,A_551)
      | ~ v1_relat_1(B_550) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4603,plain,(
    ! [A_43] :
      ( k1_relat_1(k6_partfun1(A_43)) = A_43
      | ~ v1_partfun1(k6_partfun1(A_43),A_43)
      | ~ v1_relat_1(k6_partfun1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_497,c_4597])).

tff(c_4616,plain,(
    ! [A_552] : k1_relat_1(k6_partfun1(A_552)) = A_552 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_48,c_4603])).

tff(c_4628,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4328,c_4616])).

tff(c_4308,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_4331,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | A_24 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_34])).

tff(c_62,plain,(
    ! [A_44,B_45] : m1_subset_1('#skF_2'(A_44,B_45),k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4692,plain,(
    ! [A_570,B_571,A_572] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_570,B_571))
      | ~ r2_hidden(A_572,'#skF_2'(A_570,B_571)) ) ),
    inference(resolution,[status(thm)],[c_62,c_239])).

tff(c_4708,plain,(
    ! [A_573,B_574] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_573,B_574))
      | '#skF_2'(A_573,B_574) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_4331,c_4692])).

tff(c_4718,plain,(
    '#skF_2'(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_4308,c_4708])).

tff(c_54,plain,(
    ! [A_44,B_45] : v1_funct_1('#skF_2'(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    ! [A_44,B_45] : v1_funct_2('#skF_2'(A_44,B_45),A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_68,plain,(
    ! [B_49,C_50,A_48] :
      ( k1_xboole_0 = B_49
      | v1_partfun1(C_50,A_48)
      | ~ v1_funct_2(C_50,A_48,B_49)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_4954,plain,(
    ! [B_605,C_606,A_607] :
      ( B_605 = '#skF_6'
      | v1_partfun1(C_606,A_607)
      | ~ v1_funct_2(C_606,A_607,B_605)
      | ~ m1_subset_1(C_606,k1_zfmisc_1(k2_zfmisc_1(A_607,B_605)))
      | ~ v1_funct_1(C_606) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_68])).

tff(c_4970,plain,(
    ! [B_45,A_44] :
      ( B_45 = '#skF_6'
      | v1_partfun1('#skF_2'(A_44,B_45),A_44)
      | ~ v1_funct_2('#skF_2'(A_44,B_45),A_44,B_45)
      | ~ v1_funct_1('#skF_2'(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_62,c_4954])).

tff(c_4984,plain,(
    ! [B_608,A_609] :
      ( B_608 = '#skF_6'
      | v1_partfun1('#skF_2'(A_609,B_608),A_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_4970])).

tff(c_60,plain,(
    ! [A_44,B_45] : v1_relat_1('#skF_2'(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    ! [A_44,B_45] : v4_relat_1('#skF_2'(A_44,B_45),A_44) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4606,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1('#skF_2'(A_44,B_45)) = A_44
      | ~ v1_partfun1('#skF_2'(A_44,B_45),A_44)
      | ~ v1_relat_1('#skF_2'(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_58,c_4597])).

tff(c_4615,plain,(
    ! [A_44,B_45] :
      ( k1_relat_1('#skF_2'(A_44,B_45)) = A_44
      | ~ v1_partfun1('#skF_2'(A_44,B_45),A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4606])).

tff(c_5070,plain,(
    ! [A_620,B_621] :
      ( k1_relat_1('#skF_2'(A_620,B_621)) = A_620
      | B_621 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_4984,c_4615])).

tff(c_5082,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | u1_struct_0('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_4718,c_5070])).

tff(c_5093,plain,
    ( u1_struct_0('#skF_3') = '#skF_6'
    | u1_struct_0('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_5082])).

tff(c_5097,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5093])).

tff(c_5104,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5097,c_92])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4334,plain,(
    ! [A_5] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_16])).

tff(c_4961,plain,(
    ! [B_605,A_607] :
      ( B_605 = '#skF_6'
      | v1_partfun1('#skF_6',A_607)
      | ~ v1_funct_2('#skF_6',A_607,B_605)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4334,c_4954])).

tff(c_5206,plain,(
    ! [B_626,A_627] :
      ( B_626 = '#skF_6'
      | v1_partfun1('#skF_6',A_627)
      | ~ v1_funct_2('#skF_6',A_627,B_626) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4961])).

tff(c_5219,plain,
    ( u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_5104,c_5206])).

tff(c_6005,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_5219])).

tff(c_203,plain,(
    ! [A_119,B_120] : m1_subset_1('#skF_2'(A_119,B_120),k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_209,plain,(
    ! [A_3] : m1_subset_1('#skF_2'(A_3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_203])).

tff(c_241,plain,(
    ! [A_128,A_3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_128,'#skF_2'(A_3,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_209,c_239])).

tff(c_386,plain,(
    ! [A_144,A_145] : ~ r2_hidden(A_144,'#skF_2'(A_145,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_398,plain,(
    ! [A_146] : '#skF_2'(A_146,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_386])).

tff(c_412,plain,(
    ! [A_146] : v4_relat_1(k1_xboole_0,A_146) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_58])).

tff(c_4320,plain,(
    ! [A_146] : v4_relat_1('#skF_6',A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4314,c_412])).

tff(c_4600,plain,(
    ! [A_146] :
      ( k1_relat_1('#skF_6') = A_146
      | ~ v1_partfun1('#skF_6',A_146)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4320,c_4597])).

tff(c_4609,plain,(
    ! [A_146] :
      ( k1_relat_1('#skF_6') = A_146
      | ~ v1_partfun1('#skF_6',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_4600])).

tff(c_4644,plain,(
    ! [A_146] :
      ( A_146 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4628,c_4609])).

tff(c_6011,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6005,c_4644])).

tff(c_5101,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5097,c_470])).

tff(c_6138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4336,c_4332,c_6011,c_5101])).

tff(c_6139,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5219])).

tff(c_6249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4336,c_4335,c_6139,c_5101])).

tff(c_6250,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5093])).

tff(c_6258,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6250,c_92])).

tff(c_6361,plain,(
    ! [B_695,A_696] :
      ( B_695 = '#skF_6'
      | v1_partfun1('#skF_6',A_696)
      | ~ v1_funct_2('#skF_6',A_696,B_695) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4961])).

tff(c_6374,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_6258,c_6361])).

tff(c_7147,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_6374])).

tff(c_7153,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7147,c_4644])).

tff(c_6255,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6250,c_470])).

tff(c_7379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4336,c_4332,c_7153,c_6255])).

tff(c_7380,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6374])).

tff(c_7672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4336,c_4335,c_7380,c_6255])).

tff(c_7675,plain,(
    ! [A_777] : ~ r2_hidden(A_777,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_7680,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_7675])).

tff(c_7698,plain,(
    ! [A_5] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_16])).

tff(c_8402,plain,(
    ! [B_874,C_875,A_876] :
      ( B_874 = '#skF_6'
      | v1_partfun1(C_875,A_876)
      | ~ v1_funct_2(C_875,A_876,B_874)
      | ~ m1_subset_1(C_875,k1_zfmisc_1(k2_zfmisc_1(A_876,B_874)))
      | ~ v1_funct_1(C_875) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_68])).

tff(c_8409,plain,(
    ! [B_874,A_876] :
      ( B_874 = '#skF_6'
      | v1_partfun1('#skF_6',A_876)
      | ~ v1_funct_2('#skF_6',A_876,B_874)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7698,c_8402])).

tff(c_8545,plain,(
    ! [B_891,A_892] :
      ( B_891 = '#skF_6'
      | v1_partfun1('#skF_6',A_892)
      | ~ v1_funct_2('#skF_6',A_892,B_891) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_8409])).

tff(c_8566,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_117,c_8545])).

tff(c_8568,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8566])).

tff(c_7692,plain,(
    k6_partfun1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_278])).

tff(c_7732,plain,(
    ! [C_779,A_780,B_781] :
      ( v4_relat_1(C_779,A_780)
      | ~ m1_subset_1(C_779,k1_zfmisc_1(k2_zfmisc_1(A_780,B_781))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7748,plain,(
    ! [A_43] : v4_relat_1(k6_partfun1(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_50,c_7732])).

tff(c_8079,plain,(
    ! [B_824,A_825] :
      ( k1_relat_1(B_824) = A_825
      | ~ v1_partfun1(B_824,A_825)
      | ~ v4_relat_1(B_824,A_825)
      | ~ v1_relat_1(B_824) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8082,plain,(
    ! [A_43] :
      ( k1_relat_1(k6_partfun1(A_43)) = A_43
      | ~ v1_partfun1(k6_partfun1(A_43),A_43)
      | ~ v1_relat_1(k6_partfun1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_7748,c_8079])).

tff(c_8098,plain,(
    ! [A_826] : k1_relat_1(k6_partfun1(A_826)) = A_826 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_48,c_8082])).

tff(c_8110,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_7692,c_8098])).

tff(c_7684,plain,(
    ! [A_146] : v4_relat_1('#skF_6',A_146) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_412])).

tff(c_8085,plain,(
    ! [A_146] :
      ( k1_relat_1('#skF_6') = A_146
      | ~ v1_partfun1('#skF_6',A_146)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7684,c_8079])).

tff(c_8094,plain,(
    ! [A_146] :
      ( k1_relat_1('#skF_6') = A_146
      | ~ v1_partfun1('#skF_6',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_8085])).

tff(c_8126,plain,(
    ! [A_146] :
      ( A_146 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8110,c_8094])).

tff(c_8573,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8568,c_8126])).

tff(c_8578,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8573,c_433])).

tff(c_206,plain,(
    ! [B_4] : m1_subset_1('#skF_2'(k1_xboole_0,B_4),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_203])).

tff(c_243,plain,(
    ! [A_128,B_4] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_128,'#skF_2'(k1_xboole_0,B_4)) ) ),
    inference(resolution,[status(thm)],[c_206,c_239])).

tff(c_338,plain,(
    ! [A_137,B_138] : ~ r2_hidden(A_137,'#skF_2'(k1_xboole_0,B_138)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_243])).

tff(c_343,plain,(
    ! [B_138] : '#skF_2'(k1_xboole_0,B_138) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_338])).

tff(c_7863,plain,(
    ! [B_790] : '#skF_2'('#skF_6',B_790) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_343])).

tff(c_7871,plain,(
    ! [B_790] : v1_funct_2('#skF_6','#skF_6',B_790) ),
    inference(superposition,[status(thm),theory(equality)],[c_7863,c_52])).

tff(c_7688,plain,(
    ! [B_138] : '#skF_2'('#skF_6',B_138) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_343])).

tff(c_8567,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_92,c_8545])).

tff(c_8569,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_8567])).

tff(c_10168,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8573,c_8569])).

tff(c_10172,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_10168,c_8126])).

tff(c_7696,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_6',B_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_14])).

tff(c_8631,plain,(
    ! [D_893,A_894,B_895] :
      ( v5_pre_topc(D_893,A_894,B_895)
      | ~ v5_pre_topc(D_893,g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894)),B_895)
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895))))
      | ~ v1_funct_2(D_893,u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895))
      | ~ m1_subset_1(D_893,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_894),u1_struct_0(B_895))))
      | ~ v1_funct_2(D_893,u1_struct_0(A_894),u1_struct_0(B_895))
      | ~ v1_funct_1(D_893)
      | ~ l1_pre_topc(B_895)
      | ~ v2_pre_topc(B_895)
      | ~ l1_pre_topc(A_894)
      | ~ v2_pre_topc(A_894) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_8649,plain,(
    ! [A_894,B_895] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895)),A_894,B_895)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895)),g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894)),B_895)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895)),u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_894),u1_struct_0(B_895))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895)),u1_struct_0(A_894),u1_struct_0(B_895))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894),u1_pre_topc(A_894))),u1_struct_0(B_895)))
      | ~ l1_pre_topc(B_895)
      | ~ v2_pre_topc(B_895)
      | ~ l1_pre_topc(A_894)
      | ~ v2_pre_topc(A_894) ) ),
    inference(resolution,[status(thm)],[c_62,c_8631])).

tff(c_10797,plain,(
    ! [A_1057,B_1058] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057),u1_pre_topc(A_1057))),u1_struct_0(B_1058)),A_1057,B_1058)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057),u1_pre_topc(A_1057))),u1_struct_0(B_1058)),g1_pre_topc(u1_struct_0(A_1057),u1_pre_topc(A_1057)),B_1058)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057),u1_pre_topc(A_1057))),u1_struct_0(B_1058)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1057),u1_struct_0(B_1058))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057),u1_pre_topc(A_1057))),u1_struct_0(B_1058)),u1_struct_0(A_1057),u1_struct_0(B_1058))
      | ~ l1_pre_topc(B_1058)
      | ~ v2_pre_topc(B_1058)
      | ~ l1_pre_topc(A_1057)
      | ~ v2_pre_topc(A_1057) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_8649])).

tff(c_10809,plain,(
    ! [B_1058] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_1058)),'#skF_3',B_1058)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_1058)),g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_1058)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_1058)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1058))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_1058)),u1_struct_0('#skF_3'),u1_struct_0(B_1058))
      | ~ l1_pre_topc(B_1058)
      | ~ v2_pre_topc(B_1058)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8573,c_10797])).

tff(c_11393,plain,(
    ! [B_1107] :
      ( v5_pre_topc('#skF_6','#skF_3',B_1107)
      | ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_1107)
      | ~ l1_pre_topc(B_1107)
      | ~ v2_pre_topc(B_1107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_7871,c_7688,c_10172,c_8573,c_8573,c_7698,c_7688,c_10172,c_7696,c_8573,c_8573,c_7688,c_10172,c_8573,c_7688,c_10172,c_8573,c_10809])).

tff(c_11409,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_8578,c_11393])).

tff(c_11416,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_11409])).

tff(c_11419,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_11416])).

tff(c_11423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_11419])).

tff(c_11424,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_11409])).

tff(c_11426,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_11424])).

tff(c_11429,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_456,c_11426])).

tff(c_11433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_11429])).

tff(c_11434,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_11424])).

tff(c_8491,plain,(
    ! [D_886,A_887,B_888] :
      ( v5_pre_topc(D_886,A_887,B_888)
      | ~ v5_pre_topc(D_886,A_887,g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))
      | ~ m1_subset_1(D_886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888))))))
      | ~ v1_funct_2(D_886,u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888))))
      | ~ m1_subset_1(D_886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887),u1_struct_0(B_888))))
      | ~ v1_funct_2(D_886,u1_struct_0(A_887),u1_struct_0(B_888))
      | ~ v1_funct_1(D_886)
      | ~ l1_pre_topc(B_888)
      | ~ v2_pre_topc(B_888)
      | ~ l1_pre_topc(A_887)
      | ~ v2_pre_topc(A_887) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_8503,plain,(
    ! [A_887,B_888] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))),A_887,B_888)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))),A_887,g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))),u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887),u1_struct_0(B_888))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))),u1_struct_0(A_887),u1_struct_0(B_888))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_887),u1_struct_0(g1_pre_topc(u1_struct_0(B_888),u1_pre_topc(B_888)))))
      | ~ l1_pre_topc(B_888)
      | ~ v2_pre_topc(B_888)
      | ~ l1_pre_topc(A_887)
      | ~ v2_pre_topc(A_887) ) ),
    inference(resolution,[status(thm)],[c_62,c_8491])).

tff(c_10694,plain,(
    ! [A_1044,B_1045] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_1044),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),A_1044,B_1045)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_1044),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),A_1044,g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_1044),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1044),u1_struct_0(B_1045))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_1044),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),u1_struct_0(A_1044),u1_struct_0(B_1045))
      | ~ l1_pre_topc(B_1045)
      | ~ v2_pre_topc(B_1045)
      | ~ l1_pre_topc(A_1044)
      | ~ v2_pre_topc(A_1044) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_8503])).

tff(c_10702,plain,(
    ! [B_1045] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),'#skF_3',B_1045)
      | ~ v5_pre_topc('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),'#skF_3',g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1045))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1045),u1_pre_topc(B_1045)))),u1_struct_0('#skF_3'),u1_struct_0(B_1045))
      | ~ l1_pre_topc(B_1045)
      | ~ v2_pre_topc(B_1045)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8573,c_10694])).

tff(c_11649,plain,(
    ! [B_1130] :
      ( v5_pre_topc('#skF_6','#skF_3',B_1130)
      | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_1130),u1_pre_topc(B_1130)))
      | ~ l1_pre_topc(B_1130)
      | ~ v2_pre_topc(B_1130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_7871,c_7688,c_8573,c_8573,c_7698,c_7688,c_8573,c_8573,c_7688,c_7688,c_8573,c_10702])).

tff(c_11655,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_11434,c_11649])).

tff(c_11668,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_11655])).

tff(c_11670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_11668])).

tff(c_11671,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8567])).

tff(c_11826,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11671,c_456])).

tff(c_16948,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_11826])).

tff(c_16951,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_456,c_16948])).

tff(c_16955,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_16951])).

tff(c_16957,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_11826])).

tff(c_11823,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11671,c_76])).

tff(c_17566,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16957,c_11823])).

tff(c_17567,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_17566])).

tff(c_17570,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_17567])).

tff(c_17574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_17570])).

tff(c_17576,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_17566])).

tff(c_11676,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_8568,c_8126])).

tff(c_17125,plain,(
    ! [A_1475,B_1476] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_1475),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),A_1475,B_1476)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_1475),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),A_1475,g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_1475),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1475),u1_struct_0(B_1476))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_1475),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),u1_struct_0(A_1475),u1_struct_0(B_1476))
      | ~ l1_pre_topc(B_1476)
      | ~ v2_pre_topc(B_1476)
      | ~ l1_pre_topc(A_1475)
      | ~ v2_pre_topc(A_1475) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_8503])).

tff(c_17135,plain,(
    ! [B_1476] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),'#skF_3',B_1476)
      | ~ v5_pre_topc('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),'#skF_3',g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_1476))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))),u1_struct_0('#skF_3'),u1_struct_0(B_1476))
      | ~ l1_pre_topc(B_1476)
      | ~ v2_pre_topc(B_1476)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11676,c_17125])).

tff(c_17633,plain,(
    ! [B_1530] :
      ( v5_pre_topc('#skF_6','#skF_3',B_1530)
      | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_1530),u1_pre_topc(B_1530)))
      | ~ l1_pre_topc(B_1530)
      | ~ v2_pre_topc(B_1530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_7871,c_7688,c_11676,c_11676,c_7698,c_7688,c_11676,c_11676,c_7688,c_7688,c_11676,c_17135])).

tff(c_17639,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11671,c_17633])).

tff(c_17645,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17576,c_16957,c_17639])).

tff(c_17649,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_17645])).

tff(c_16443,plain,(
    ! [D_1405,A_1406,B_1407] :
      ( v5_pre_topc(D_1405,A_1406,g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))
      | ~ v5_pre_topc(D_1405,A_1406,B_1407)
      | ~ m1_subset_1(D_1405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407))))))
      | ~ v1_funct_2(D_1405,u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407))))
      | ~ m1_subset_1(D_1405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1406),u1_struct_0(B_1407))))
      | ~ v1_funct_2(D_1405,u1_struct_0(A_1406),u1_struct_0(B_1407))
      | ~ v1_funct_1(D_1405)
      | ~ l1_pre_topc(B_1407)
      | ~ v2_pre_topc(B_1407)
      | ~ l1_pre_topc(A_1406)
      | ~ v2_pre_topc(A_1406) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_16470,plain,(
    ! [A_1406,B_1407] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))),A_1406,g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))),A_1406,B_1407)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))),u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1406),u1_struct_0(B_1407))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))),u1_struct_0(A_1406),u1_struct_0(B_1407))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_1406),u1_struct_0(g1_pre_topc(u1_struct_0(B_1407),u1_pre_topc(B_1407)))))
      | ~ l1_pre_topc(B_1407)
      | ~ v2_pre_topc(B_1407)
      | ~ l1_pre_topc(A_1406)
      | ~ v2_pre_topc(A_1406) ) ),
    inference(resolution,[status(thm)],[c_62,c_16443])).

tff(c_16988,plain,(
    ! [A_1466,B_1467] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_1466),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),A_1466,g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_1466),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),A_1466,B_1467)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_1466),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1466),u1_struct_0(B_1467))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_1466),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),u1_struct_0(A_1466),u1_struct_0(B_1467))
      | ~ l1_pre_topc(B_1467)
      | ~ v2_pre_topc(B_1467)
      | ~ l1_pre_topc(A_1466)
      | ~ v2_pre_topc(A_1466) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_16470])).

tff(c_17004,plain,(
    ! [B_1467] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),'#skF_3',g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),'#skF_3',B_1467)
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0(B_1467))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1467),u1_pre_topc(B_1467)))),u1_struct_0('#skF_3'),u1_struct_0(B_1467))
      | ~ l1_pre_topc(B_1467)
      | ~ v2_pre_topc(B_1467)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11676,c_16988])).

tff(c_17553,plain,(
    ! [B_1528] :
      ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_1528),u1_pre_topc(B_1528)))
      | ~ v5_pre_topc('#skF_6','#skF_3',B_1528)
      | ~ l1_pre_topc(B_1528)
      | ~ v2_pre_topc(B_1528) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_7871,c_7688,c_11676,c_11676,c_7698,c_7688,c_11676,c_7688,c_11676,c_7688,c_11676,c_17004])).

tff(c_17556,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_11671,c_17553])).

tff(c_17561,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16957,c_17556])).

tff(c_19578,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17576,c_17561])).

tff(c_19579,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_17649,c_19578])).

tff(c_11681,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11676,c_433])).

tff(c_409,plain,(
    ! [A_146] : v1_funct_2(k1_xboole_0,A_146,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_52])).

tff(c_7683,plain,(
    ! [A_146] : v1_funct_2('#skF_6',A_146,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_409])).

tff(c_394,plain,(
    ! [A_145] : '#skF_2'(A_145,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_386])).

tff(c_7685,plain,(
    ! [A_145] : '#skF_2'(A_145,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_394])).

tff(c_11734,plain,(
    ! [D_1131,A_1132,B_1133] :
      ( v5_pre_topc(D_1131,A_1132,B_1133)
      | ~ v5_pre_topc(D_1131,g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132)),B_1133)
      | ~ m1_subset_1(D_1131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133))))
      | ~ v1_funct_2(D_1131,u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133))
      | ~ m1_subset_1(D_1131,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1132),u1_struct_0(B_1133))))
      | ~ v1_funct_2(D_1131,u1_struct_0(A_1132),u1_struct_0(B_1133))
      | ~ v1_funct_1(D_1131)
      | ~ l1_pre_topc(B_1133)
      | ~ v2_pre_topc(B_1133)
      | ~ l1_pre_topc(A_1132)
      | ~ v2_pre_topc(A_1132) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_11752,plain,(
    ! [A_1132,B_1133] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133)),A_1132,B_1133)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133)),g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132)),B_1133)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133)),u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1132),u1_struct_0(B_1133))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133)),u1_struct_0(A_1132),u1_struct_0(B_1133))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132),u1_pre_topc(A_1132))),u1_struct_0(B_1133)))
      | ~ l1_pre_topc(B_1133)
      | ~ v2_pre_topc(B_1133)
      | ~ l1_pre_topc(A_1132)
      | ~ v2_pre_topc(A_1132) ) ),
    inference(resolution,[status(thm)],[c_62,c_11734])).

tff(c_17263,plain,(
    ! [A_1496,B_1497] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(B_1497)),A_1496,B_1497)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(B_1497)),g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496)),B_1497)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(B_1497)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1496),u1_struct_0(B_1497))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(B_1497)),u1_struct_0(A_1496),u1_struct_0(B_1497))
      | ~ l1_pre_topc(B_1497)
      | ~ v2_pre_topc(B_1497)
      | ~ l1_pre_topc(A_1496)
      | ~ v2_pre_topc(A_1496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_11752])).

tff(c_17269,plain,(
    ! [A_1496] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_1496,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),'#skF_6'),g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1496),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_1496),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_1496)
      | ~ v2_pre_topc(A_1496) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11671,c_17263])).

tff(c_17283,plain,(
    ! [A_1496] :
      ( v5_pre_topc('#skF_6',A_1496,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_1496),u1_pre_topc(A_1496)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_1496)
      | ~ v2_pre_topc(A_1496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16957,c_7683,c_7685,c_11671,c_11671,c_7698,c_7685,c_11671,c_11671,c_7685,c_7685,c_11671,c_17269])).

tff(c_19838,plain,(
    ! [A_1648] :
      ( v5_pre_topc('#skF_6',A_1648,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_1648),u1_pre_topc(A_1648)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_1648)
      | ~ v2_pre_topc(A_1648) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17576,c_17283])).

tff(c_19858,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11676,c_19838])).

tff(c_19873,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_11681,c_19858])).

tff(c_19875,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19579,c_19873])).

tff(c_19876,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_17645])).

tff(c_17149,plain,(
    ! [B_1476] :
      ( v5_pre_topc('#skF_6','#skF_3',B_1476)
      | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_1476),u1_pre_topc(B_1476)))
      | ~ l1_pre_topc(B_1476)
      | ~ v2_pre_topc(B_1476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_7871,c_7688,c_11676,c_11676,c_7698,c_7688,c_11676,c_11676,c_7688,c_7688,c_11676,c_17135])).

tff(c_19880,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_19876,c_17149])).

tff(c_19883,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_19880])).

tff(c_19885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_19883])).

tff(c_19886,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_8566])).

tff(c_19891,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19886,c_433])).

tff(c_28114,plain,
    ( u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19886,c_8567])).

tff(c_28115,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_28114])).

tff(c_28179,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_28115,c_8126])).

tff(c_7852,plain,(
    ! [A_787,B_788] :
      ( v1_pre_topc(g1_pre_topc(A_787,B_788))
      | ~ m1_subset_1(B_788,k1_zfmisc_1(k1_zfmisc_1(A_787))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_7861,plain,(
    ! [A_53] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_74,c_7852])).

tff(c_28222,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28179,c_7861])).

tff(c_28994,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_28222])).

tff(c_28997,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_456,c_28994])).

tff(c_29001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_28997])).

tff(c_29003,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_28222])).

tff(c_7695,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | A_24 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_34])).

tff(c_28231,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28179,c_74])).

tff(c_29306,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29003,c_28231])).

tff(c_18,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29323,plain,(
    ! [A_2220] :
      ( m1_subset_1(A_2220,k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_2220,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ) ),
    inference(resolution,[status(thm)],[c_29306,c_18])).

tff(c_29328,plain,
    ( m1_subset_1('#skF_1'(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),k1_zfmisc_1('#skF_6'))
    | u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_7695,c_29323])).

tff(c_29599,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_29328])).

tff(c_29754,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_6'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_29599,c_76])).

tff(c_29824,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6','#skF_6'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29003,c_28179,c_29754])).

tff(c_29830,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_29824])).

tff(c_29833,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_29830])).

tff(c_29837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_29833])).

tff(c_29839,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_29824])).

tff(c_28141,plain,(
    ! [D_2102,A_2103,B_2104] :
      ( v5_pre_topc(D_2102,g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103)),B_2104)
      | ~ v5_pre_topc(D_2102,A_2103,B_2104)
      | ~ m1_subset_1(D_2102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104))))
      | ~ v1_funct_2(D_2102,u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104))
      | ~ m1_subset_1(D_2102,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2103),u1_struct_0(B_2104))))
      | ~ v1_funct_2(D_2102,u1_struct_0(A_2103),u1_struct_0(B_2104))
      | ~ v1_funct_1(D_2102)
      | ~ l1_pre_topc(B_2104)
      | ~ v2_pre_topc(B_2104)
      | ~ l1_pre_topc(A_2103)
      | ~ v2_pre_topc(A_2103) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_28159,plain,(
    ! [A_2103,B_2104] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104)),g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103)),B_2104)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104)),A_2103,B_2104)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104)),u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2103),u1_struct_0(B_2104))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104)),u1_struct_0(A_2103),u1_struct_0(B_2104))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103),u1_pre_topc(A_2103))),u1_struct_0(B_2104)))
      | ~ l1_pre_topc(B_2104)
      | ~ v2_pre_topc(B_2104)
      | ~ l1_pre_topc(A_2103)
      | ~ v2_pre_topc(A_2103) ) ),
    inference(resolution,[status(thm)],[c_62,c_28141])).

tff(c_29004,plain,(
    ! [A_2195,B_2196] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0(B_2196)),g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195)),B_2196)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0(B_2196)),A_2195,B_2196)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0(B_2196)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195),u1_struct_0(B_2196))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0(B_2196)),u1_struct_0(A_2195),u1_struct_0(B_2196))
      | ~ l1_pre_topc(B_2196)
      | ~ v2_pre_topc(B_2196)
      | ~ l1_pre_topc(A_2195)
      | ~ v2_pre_topc(A_2195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_28159])).

tff(c_29024,plain,(
    ! [A_2195] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0('#skF_4')),g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195)),'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0('#skF_4')),A_2195,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195))),u1_struct_0('#skF_4')),u1_struct_0(A_2195),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_2195)
      | ~ v2_pre_topc(A_2195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19886,c_29004])).

tff(c_29044,plain,(
    ! [A_2195] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2195),u1_pre_topc(A_2195)),'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_2195,'#skF_4')
      | ~ l1_pre_topc(A_2195)
      | ~ v2_pre_topc(A_2195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_7683,c_7685,c_19886,c_19886,c_7698,c_7685,c_19886,c_7685,c_19886,c_7685,c_19886,c_29024])).

tff(c_29706,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_6'),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_29599,c_29044])).

tff(c_29788,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6','#skF_6'),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29003,c_28179,c_29706])).

tff(c_30095,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6','#skF_6'),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29839,c_29788])).

tff(c_30096,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30095])).

tff(c_7699,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7680,c_7680,c_12])).

tff(c_84,plain,(
    ! [D_84,A_70,B_78] :
      ( v5_pre_topc(D_84,A_70,B_78)
      | ~ v5_pre_topc(D_84,A_70,g1_pre_topc(u1_struct_0(B_78),u1_pre_topc(B_78)))
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(g1_pre_topc(u1_struct_0(B_78),u1_pre_topc(B_78))))))
      | ~ v1_funct_2(D_84,u1_struct_0(A_70),u1_struct_0(g1_pre_topc(u1_struct_0(B_78),u1_pre_topc(B_78))))
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(B_78))))
      | ~ v1_funct_2(D_84,u1_struct_0(A_70),u1_struct_0(B_78))
      | ~ v1_funct_1(D_84)
      | ~ l1_pre_topc(B_78)
      | ~ v2_pre_topc(B_78)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_19901,plain,(
    ! [D_84,A_70] :
      ( v5_pre_topc(D_84,A_70,'#skF_4')
      | ~ v5_pre_topc(D_84,A_70,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2(D_84,u1_struct_0(A_70),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_84,u1_struct_0(A_70),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_84)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19886,c_84])).

tff(c_32254,plain,(
    ! [D_2339,A_2340] :
      ( v5_pre_topc(D_2339,A_2340,'#skF_4')
      | ~ v5_pre_topc(D_2339,A_2340,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ m1_subset_1(D_2339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2340),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2(D_2339,u1_struct_0(A_2340),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(D_2339,k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2(D_2339,u1_struct_0(A_2340),'#skF_6')
      | ~ v1_funct_1(D_2339)
      | ~ l1_pre_topc(A_2340)
      | ~ v2_pre_topc(A_2340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_19886,c_7699,c_19886,c_19886,c_19886,c_19901])).

tff(c_32276,plain,(
    ! [A_2340] :
      ( v5_pre_topc('#skF_6',A_2340,'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_2340,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2340),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2340),'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(A_2340)
      | ~ v2_pre_topc(A_2340) ) ),
    inference(resolution,[status(thm)],[c_7698,c_32254])).

tff(c_32308,plain,(
    ! [A_2341] :
      ( v5_pre_topc('#skF_6',A_2341,'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_2341,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2341),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(A_2341)
      | ~ v2_pre_topc(A_2341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_7683,c_7698,c_32276])).

tff(c_32311,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
    | ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28179,c_32308])).

tff(c_32319,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29839,c_29003,c_7871,c_19891,c_32311])).

tff(c_32321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30096,c_32319])).

tff(c_32323,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_30095])).

tff(c_28285,plain,(
    ! [D_2110,A_2111,B_2112] :
      ( v5_pre_topc(D_2110,A_2111,B_2112)
      | ~ v5_pre_topc(D_2110,g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111)),B_2112)
      | ~ m1_subset_1(D_2110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112))))
      | ~ v1_funct_2(D_2110,u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112))
      | ~ m1_subset_1(D_2110,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2111),u1_struct_0(B_2112))))
      | ~ v1_funct_2(D_2110,u1_struct_0(A_2111),u1_struct_0(B_2112))
      | ~ v1_funct_1(D_2110)
      | ~ l1_pre_topc(B_2112)
      | ~ v2_pre_topc(B_2112)
      | ~ l1_pre_topc(A_2111)
      | ~ v2_pre_topc(A_2111) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_28312,plain,(
    ! [A_2111,B_2112] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112)),A_2111,B_2112)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112)),g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111)),B_2112)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112)),u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2111),u1_struct_0(B_2112))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112)),u1_struct_0(A_2111),u1_struct_0(B_2112))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111),u1_pre_topc(A_2111))),u1_struct_0(B_2112)))
      | ~ l1_pre_topc(B_2112)
      | ~ v2_pre_topc(B_2112)
      | ~ l1_pre_topc(A_2111)
      | ~ v2_pre_topc(A_2111) ) ),
    inference(resolution,[status(thm)],[c_62,c_28285])).

tff(c_28673,plain,(
    ! [A_2150,B_2151] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0(B_2151)),A_2150,B_2151)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0(B_2151)),g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150)),B_2151)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0(B_2151)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2150),u1_struct_0(B_2151))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0(B_2151)),u1_struct_0(A_2150),u1_struct_0(B_2151))
      | ~ l1_pre_topc(B_2151)
      | ~ v2_pre_topc(B_2151)
      | ~ l1_pre_topc(A_2150)
      | ~ v2_pre_topc(A_2150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_28312])).

tff(c_28685,plain,(
    ! [A_2150] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0('#skF_4')),A_2150,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),'#skF_6'),g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150)),'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2150),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150))),u1_struct_0('#skF_4')),u1_struct_0(A_2150),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_2150)
      | ~ v2_pre_topc(A_2150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19886,c_28673])).

tff(c_28697,plain,(
    ! [A_2150] :
      ( v5_pre_topc('#skF_6',A_2150,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2150),u1_pre_topc(A_2150)),'#skF_4')
      | ~ l1_pre_topc(A_2150)
      | ~ v2_pre_topc(A_2150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_7683,c_7685,c_19886,c_19886,c_7698,c_7685,c_19886,c_19886,c_7685,c_7685,c_19886,c_28685])).

tff(c_32388,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32323,c_28697])).

tff(c_32391,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_32388])).

tff(c_32393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_32391])).

tff(c_32394,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_28114])).

tff(c_33278,plain,(
    ! [A_2418,B_2419] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0(B_2419),u1_pre_topc(B_2419)))),A_2418,B_2419)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0(B_2419),u1_pre_topc(B_2419)))),A_2418,g1_pre_topc(u1_struct_0(B_2419),u1_pre_topc(B_2419)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0(B_2419),u1_pre_topc(B_2419)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2418),u1_struct_0(B_2419))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0(B_2419),u1_pre_topc(B_2419)))),u1_struct_0(A_2418),u1_struct_0(B_2419))
      | ~ l1_pre_topc(B_2419)
      | ~ v2_pre_topc(B_2419)
      | ~ l1_pre_topc(A_2418)
      | ~ v2_pre_topc(A_2418) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_8503])).

tff(c_33294,plain,(
    ! [A_2418] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_2418,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_2418,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2418),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_2418),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_2418),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_2418)
      | ~ v2_pre_topc(A_2418) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19886,c_33278])).

tff(c_33615,plain,(
    ! [A_2458] :
      ( v5_pre_topc('#skF_6',A_2458,'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_2458,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_2458)
      | ~ v2_pre_topc(A_2458) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_7683,c_7685,c_32394,c_19886,c_19886,c_7698,c_7685,c_32394,c_7699,c_19886,c_19886,c_7685,c_32394,c_19886,c_7685,c_32394,c_19886,c_33294])).

tff(c_33630,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_19891,c_33615])).

tff(c_33713,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_33630])).

tff(c_33716,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_33713])).

tff(c_33720,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_33716])).

tff(c_33721,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_33630])).

tff(c_33723,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_33721])).

tff(c_33726,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_456,c_33723])).

tff(c_33730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_33726])).

tff(c_33731,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_33721])).

tff(c_32592,plain,(
    ! [D_2354,A_2355,B_2356] :
      ( v5_pre_topc(D_2354,A_2355,B_2356)
      | ~ v5_pre_topc(D_2354,g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355)),B_2356)
      | ~ m1_subset_1(D_2354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356))))
      | ~ v1_funct_2(D_2354,u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356))
      | ~ m1_subset_1(D_2354,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2355),u1_struct_0(B_2356))))
      | ~ v1_funct_2(D_2354,u1_struct_0(A_2355),u1_struct_0(B_2356))
      | ~ v1_funct_1(D_2354)
      | ~ l1_pre_topc(B_2356)
      | ~ v2_pre_topc(B_2356)
      | ~ l1_pre_topc(A_2355)
      | ~ v2_pre_topc(A_2355) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_32616,plain,(
    ! [A_2355,B_2356] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356)),A_2355,B_2356)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356)),g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355)),B_2356)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356)),u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2355),u1_struct_0(B_2356))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356)),u1_struct_0(A_2355),u1_struct_0(B_2356))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355),u1_pre_topc(A_2355))),u1_struct_0(B_2356)))
      | ~ l1_pre_topc(B_2356)
      | ~ v2_pre_topc(B_2356)
      | ~ l1_pre_topc(A_2355)
      | ~ v2_pre_topc(A_2355) ) ),
    inference(resolution,[status(thm)],[c_62,c_32592])).

tff(c_32999,plain,(
    ! [A_2393,B_2394] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0(B_2394)),A_2393,B_2394)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0(B_2394)),g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393)),B_2394)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0(B_2394)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2393),u1_struct_0(B_2394))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0(B_2394)),u1_struct_0(A_2393),u1_struct_0(B_2394))
      | ~ l1_pre_topc(B_2394)
      | ~ v2_pre_topc(B_2394)
      | ~ l1_pre_topc(A_2393)
      | ~ v2_pre_topc(A_2393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_32616])).

tff(c_33009,plain,(
    ! [A_2393] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0('#skF_4')),A_2393,'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),'#skF_6'),g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393)),'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0('#skF_4')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2393),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393),u1_pre_topc(A_2393))),u1_struct_0('#skF_4')),u1_struct_0(A_2393),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_2393)
      | ~ v2_pre_topc(A_2393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19886,c_32999])).

tff(c_33971,plain,(
    ! [A_2476] :
      ( v5_pre_topc('#skF_6',A_2476,'#skF_4')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2476),u1_pre_topc(A_2476)),'#skF_4')
      | ~ l1_pre_topc(A_2476)
      | ~ v2_pre_topc(A_2476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_7683,c_7685,c_19886,c_19886,c_7698,c_7685,c_19886,c_19886,c_7685,c_7685,c_19886,c_33009])).

tff(c_33977,plain,
    ( v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_33731,c_33971])).

tff(c_33990,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_33977])).

tff(c_33992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_33990])).

tff(c_33994,plain,(
    v5_pre_topc('#skF_6','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_34204,plain,(
    ! [C_2506,A_2507,B_2508] :
      ( v4_relat_1(C_2506,A_2507)
      | ~ m1_subset_1(C_2506,k1_zfmisc_1(k2_zfmisc_1(A_2507,B_2508))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34229,plain,(
    v4_relat_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_121,c_34204])).

tff(c_34354,plain,(
    ! [B_2541,A_2542] :
      ( k1_relat_1(B_2541) = A_2542
      | ~ v1_partfun1(B_2541,A_2542)
      | ~ v4_relat_1(B_2541,A_2542)
      | ~ v1_relat_1(B_2541) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34363,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34229,c_34354])).

tff(c_34378,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_34363])).

tff(c_34420,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34378])).

tff(c_34757,plain,(
    ! [B_2596,C_2597,A_2598] :
      ( k1_xboole_0 = B_2596
      | v1_partfun1(C_2597,A_2598)
      | ~ v1_funct_2(C_2597,A_2598,B_2596)
      | ~ m1_subset_1(C_2597,k1_zfmisc_1(k2_zfmisc_1(A_2598,B_2596)))
      | ~ v1_funct_1(C_2597) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_34769,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_121,c_34757])).

tff(c_34795,plain,
    ( u1_struct_0('#skF_4') = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_117,c_34769])).

tff(c_34796,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34420,c_34795])).

tff(c_34253,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_263])).

tff(c_34812,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34796,c_34253])).

tff(c_34822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_34812])).

tff(c_34823,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_34378])).

tff(c_33993,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_34827,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34823,c_33993])).

tff(c_34833,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34823,c_90])).

tff(c_35086,plain,(
    ! [D_2630,B_2631,C_2632,A_2633] :
      ( m1_subset_1(D_2630,k1_zfmisc_1(k2_zfmisc_1(B_2631,C_2632)))
      | ~ r1_tarski(k1_relat_1(D_2630),B_2631)
      | ~ m1_subset_1(D_2630,k1_zfmisc_1(k2_zfmisc_1(A_2633,C_2632))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_35102,plain,(
    ! [B_2631] :
      ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_2631,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ r1_tarski(k1_relat_1('#skF_6'),B_2631) ) ),
    inference(resolution,[status(thm)],[c_34833,c_35086])).

tff(c_35551,plain,(
    ! [D_2677,A_2678,B_2679] :
      ( v5_pre_topc(D_2677,A_2678,B_2679)
      | ~ v5_pre_topc(D_2677,g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678)),B_2679)
      | ~ m1_subset_1(D_2677,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678))),u1_struct_0(B_2679))))
      | ~ v1_funct_2(D_2677,u1_struct_0(g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678))),u1_struct_0(B_2679))
      | ~ m1_subset_1(D_2677,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2678),u1_struct_0(B_2679))))
      | ~ v1_funct_2(D_2677,u1_struct_0(A_2678),u1_struct_0(B_2679))
      | ~ v1_funct_1(D_2677)
      | ~ l1_pre_topc(B_2679)
      | ~ v2_pre_topc(B_2679)
      | ~ l1_pre_topc(A_2678)
      | ~ v2_pre_topc(A_2678) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_35559,plain,(
    ! [A_2678] :
      ( v5_pre_topc('#skF_6',A_2678,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2678),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2678),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_2678)
      | ~ v2_pre_topc(A_2678)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678)))) ) ),
    inference(resolution,[status(thm)],[c_35102,c_35551])).

tff(c_35587,plain,(
    ! [A_2678] :
      ( v5_pre_topc('#skF_6',A_2678,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2678),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2678),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_2678)
      | ~ v2_pre_topc(A_2678)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2678),u1_pre_topc(A_2678)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_35559])).

tff(c_37405,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_35587])).

tff(c_37408,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_37405])).

tff(c_37412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_37408])).

tff(c_37414,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_35587])).

tff(c_35946,plain,(
    ! [D_2709,A_2710,B_2711] :
      ( v5_pre_topc(D_2709,g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)),B_2711)
      | ~ v5_pre_topc(D_2709,A_2710,B_2711)
      | ~ m1_subset_1(D_2709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710))),u1_struct_0(B_2711))))
      | ~ v1_funct_2(D_2709,u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710))),u1_struct_0(B_2711))
      | ~ m1_subset_1(D_2709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710),u1_struct_0(B_2711))))
      | ~ v1_funct_2(D_2709,u1_struct_0(A_2710),u1_struct_0(B_2711))
      | ~ v1_funct_1(D_2709)
      | ~ l1_pre_topc(B_2711)
      | ~ v2_pre_topc(B_2711)
      | ~ l1_pre_topc(A_2710)
      | ~ v2_pre_topc(A_2710) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_35964,plain,(
    ! [A_2710] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_2710,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2710),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_2710)
      | ~ v2_pre_topc(A_2710)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)))) ) ),
    inference(resolution,[status(thm)],[c_35102,c_35946])).

tff(c_35999,plain,(
    ! [A_2710] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_2710,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2710),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_2710)
      | ~ v2_pre_topc(A_2710)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_35964])).

tff(c_37507,plain,(
    ! [A_2710] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_2710,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2710),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_2710)
      | ~ v2_pre_topc(A_2710)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(A_2710),u1_pre_topc(A_2710)))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37414,c_35999])).

tff(c_37508,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_37507])).

tff(c_37511,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34171,c_37508])).

tff(c_37515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_37511])).

tff(c_37517,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_37507])).

tff(c_34834,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34823,c_92])).

tff(c_35277,plain,(
    ! [B_2648,C_2649,A_2650] :
      ( k1_xboole_0 = B_2648
      | v1_partfun1(C_2649,A_2650)
      | ~ v1_funct_2(C_2649,A_2650,B_2648)
      | ~ m1_subset_1(C_2649,k1_zfmisc_1(k2_zfmisc_1(A_2650,B_2648)))
      | ~ v1_funct_1(C_2649) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_35286,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34833,c_35277])).

tff(c_35312,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_xboole_0
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_34834,c_35286])).

tff(c_35624,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_35312])).

tff(c_34231,plain,(
    v4_relat_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_90,c_34204])).

tff(c_34357,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34231,c_34354])).

tff(c_34372,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_34357])).

tff(c_35841,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35624,c_34823,c_34823,c_34372])).

tff(c_35847,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35841,c_34834])).

tff(c_34832,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34823,c_117])).

tff(c_34831,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34823,c_121])).

tff(c_35424,plain,(
    ! [D_2664,A_2665,B_2666] :
      ( v5_pre_topc(D_2664,A_2665,g1_pre_topc(u1_struct_0(B_2666),u1_pre_topc(B_2666)))
      | ~ v5_pre_topc(D_2664,A_2665,B_2666)
      | ~ m1_subset_1(D_2664,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2665),u1_struct_0(g1_pre_topc(u1_struct_0(B_2666),u1_pre_topc(B_2666))))))
      | ~ v1_funct_2(D_2664,u1_struct_0(A_2665),u1_struct_0(g1_pre_topc(u1_struct_0(B_2666),u1_pre_topc(B_2666))))
      | ~ m1_subset_1(D_2664,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2665),u1_struct_0(B_2666))))
      | ~ v1_funct_2(D_2664,u1_struct_0(A_2665),u1_struct_0(B_2666))
      | ~ v1_funct_1(D_2664)
      | ~ l1_pre_topc(B_2666)
      | ~ v2_pre_topc(B_2666)
      | ~ l1_pre_topc(A_2665)
      | ~ v2_pre_topc(A_2665) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_35428,plain,(
    ! [A_2665] :
      ( v5_pre_topc('#skF_6',A_2665,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_2665,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2665),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2665),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2665),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_2665)
      | ~ v2_pre_topc(A_2665)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(A_2665)) ) ),
    inference(resolution,[status(thm)],[c_35102,c_35424])).

tff(c_37063,plain,(
    ! [A_2830] :
      ( v5_pre_topc('#skF_6',A_2830,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_2830,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2830),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2830),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_2830),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc(A_2830)
      | ~ v2_pre_topc(A_2830)
      | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0(A_2830)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_94,c_35428])).

tff(c_37072,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34823,c_37063])).

tff(c_37078,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_34823,c_108,c_106,c_34832,c_34823,c_34831,c_34823,c_35847,c_33994,c_37072])).

tff(c_35846,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35841,c_34833])).

tff(c_35971,plain,(
    ! [D_2709,B_2711] :
      ( v5_pre_topc(D_2709,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_2711)
      | ~ v5_pre_topc(D_2709,'#skF_3',B_2711)
      | ~ m1_subset_1(D_2709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(B_2711))))
      | ~ v1_funct_2(D_2709,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_2711))
      | ~ m1_subset_1(D_2709,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_2711))))
      | ~ v1_funct_2(D_2709,u1_struct_0('#skF_3'),u1_struct_0(B_2711))
      | ~ v1_funct_1(D_2709)
      | ~ l1_pre_topc(B_2711)
      | ~ v2_pre_topc(B_2711)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34823,c_35946])).

tff(c_38020,plain,(
    ! [D_2886,B_2887] :
      ( v5_pre_topc(D_2886,g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),B_2887)
      | ~ v5_pre_topc(D_2886,'#skF_3',B_2887)
      | ~ m1_subset_1(D_2886,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_2887))))
      | ~ v1_funct_2(D_2886,k1_relat_1('#skF_6'),u1_struct_0(B_2887))
      | ~ v1_funct_1(D_2886)
      | ~ l1_pre_topc(B_2887)
      | ~ v2_pre_topc(B_2887) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_34823,c_34823,c_35841,c_34823,c_35841,c_34823,c_35971])).

tff(c_38027,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_35846,c_38020])).

tff(c_38064,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37414,c_37517,c_94,c_35847,c_37078,c_38027])).

tff(c_38066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34827,c_38064])).

tff(c_38067,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_35312])).

tff(c_34180,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_268])).

tff(c_34982,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34823,c_34180])).

tff(c_38071,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_3'))),k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38067,c_34982])).

tff(c_38079,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12,c_38071])).

tff(c_38082,plain,(
    ! [A_2888] : ~ r2_hidden(A_2888,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_38087,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_38082])).

tff(c_38109,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_2])).

tff(c_38108,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_38087,c_12])).

tff(c_38105,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_6',B_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_38087,c_14])).

tff(c_38081,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_263])).

tff(c_38104,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | A_24 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_34])).

tff(c_38484,plain,(
    ! [A_2929,B_2930,A_2931] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_2929,B_2930))
      | ~ r2_hidden(A_2931,'#skF_2'(A_2929,B_2930)) ) ),
    inference(resolution,[status(thm)],[c_62,c_239])).

tff(c_38545,plain,(
    ! [A_2938,B_2939] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_2938,B_2939))
      | '#skF_2'(A_2938,B_2939) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_38104,c_38484])).

tff(c_38555,plain,(
    '#skF_2'(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38081,c_38545])).

tff(c_38630,plain,(
    ! [B_2955,C_2956,A_2957] :
      ( B_2955 = '#skF_6'
      | v1_partfun1(C_2956,A_2957)
      | ~ v1_funct_2(C_2956,A_2957,B_2955)
      | ~ m1_subset_1(C_2956,k1_zfmisc_1(k2_zfmisc_1(A_2957,B_2955)))
      | ~ v1_funct_1(C_2956) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_68])).

tff(c_38643,plain,(
    ! [B_45,A_44] :
      ( B_45 = '#skF_6'
      | v1_partfun1('#skF_2'(A_44,B_45),A_44)
      | ~ v1_funct_2('#skF_2'(A_44,B_45),A_44,B_45)
      | ~ v1_funct_1('#skF_2'(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_62,c_38630])).

tff(c_38656,plain,(
    ! [B_2958,A_2959] :
      ( B_2958 = '#skF_6'
      | v1_partfun1('#skF_2'(A_2959,B_2958),A_2959) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38643])).

tff(c_38659,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38555,c_38656])).

tff(c_38668,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_38659])).

tff(c_34026,plain,(
    ! [A_2482] : ~ r2_hidden(A_2482,k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_249])).

tff(c_34031,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_34026])).

tff(c_38100,plain,(
    k6_partfun1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_38087,c_34031])).

tff(c_34230,plain,(
    ! [A_43] : v4_relat_1(k6_partfun1(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_50,c_34204])).

tff(c_38381,plain,(
    ! [B_2913,A_2914] :
      ( k1_relat_1(B_2913) = A_2914
      | ~ v1_partfun1(B_2913,A_2914)
      | ~ v4_relat_1(B_2913,A_2914)
      | ~ v1_relat_1(B_2913) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38387,plain,(
    ! [A_43] :
      ( k1_relat_1(k6_partfun1(A_43)) = A_43
      | ~ v1_partfun1(k6_partfun1(A_43),A_43)
      | ~ v1_relat_1(k6_partfun1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_34230,c_38381])).

tff(c_38400,plain,(
    ! [A_2915] : k1_relat_1(k6_partfun1(A_2915)) = A_2915 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_48,c_38387])).

tff(c_38412,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_38100,c_38400])).

tff(c_34064,plain,(
    ! [A_2485,A_2486] : ~ r2_hidden(A_2485,'#skF_2'(A_2486,k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_241])).

tff(c_34073,plain,(
    ! [A_2487] : '#skF_2'(A_2487,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_34064])).

tff(c_34087,plain,(
    ! [A_2487] : v4_relat_1(k1_xboole_0,A_2487) ),
    inference(superposition,[status(thm),theory(equality)],[c_34073,c_58])).

tff(c_38096,plain,(
    ! [A_2487] : v4_relat_1('#skF_6',A_2487) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_34087])).

tff(c_38384,plain,(
    ! [A_2487] :
      ( k1_relat_1('#skF_6') = A_2487
      | ~ v1_partfun1('#skF_6',A_2487)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38096,c_38381])).

tff(c_38393,plain,(
    ! [A_2487] :
      ( k1_relat_1('#skF_6') = A_2487
      | ~ v1_partfun1('#skF_6',A_2487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_38384])).

tff(c_38428,plain,(
    ! [A_2487] :
      ( A_2487 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_2487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38412,c_38393])).

tff(c_38672,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_38668,c_38428])).

tff(c_38680,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38672,c_92])).

tff(c_38107,plain,(
    ! [A_5] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38087,c_16])).

tff(c_38634,plain,(
    ! [B_2955,A_2957] :
      ( B_2955 = '#skF_6'
      | v1_partfun1('#skF_6',A_2957)
      | ~ v1_funct_2('#skF_6',A_2957,B_2955)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_38107,c_38630])).

tff(c_38767,plain,(
    ! [B_2964,A_2965] :
      ( B_2964 = '#skF_6'
      | v1_partfun1('#skF_6',A_2965)
      | ~ v1_funct_2('#skF_6',A_2965,B_2964) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_38634])).

tff(c_38780,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_38680,c_38767])).

tff(c_39809,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_38780])).

tff(c_39815,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_39809,c_38428])).

tff(c_38677,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38672,c_34180])).

tff(c_40075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38109,c_38105,c_39815,c_38677])).

tff(c_40076,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38780])).

tff(c_40370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38109,c_38108,c_40076,c_38677])).

tff(c_40371,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38659])).

tff(c_40379,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40371,c_92])).

tff(c_40465,plain,(
    ! [B_3087,A_3088] :
      ( B_3087 = '#skF_6'
      | v1_partfun1('#skF_6',A_3088)
      | ~ v1_funct_2('#skF_6',A_3088,B_3087) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_38634])).

tff(c_40478,plain,
    ( u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_40379,c_40465])).

tff(c_41656,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_40478])).

tff(c_41662,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_41656,c_38428])).

tff(c_40376,plain,(
    ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40371,c_34180])).

tff(c_41970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38109,c_38105,c_41662,c_40376])).

tff(c_41971,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_40478])).

tff(c_42245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38109,c_38108,c_41971,c_40376])).

tff(c_42248,plain,(
    ! [A_3217] : ~ r2_hidden(A_3217,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_42253,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_34,c_42248])).

tff(c_34069,plain,(
    ! [A_2486] : '#skF_2'(A_2486,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_34064])).

tff(c_42389,plain,(
    ! [A_3226] : '#skF_2'(A_3226,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_34069])).

tff(c_42397,plain,(
    ! [A_3226] : v1_funct_2('#skF_6',A_3226,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42389,c_52])).

tff(c_42261,plain,(
    ! [A_2486] : '#skF_2'(A_2486,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_34069])).

tff(c_42271,plain,(
    ! [A_5] : m1_subset_1('#skF_6',k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_16])).

tff(c_43013,plain,(
    ! [B_3325,C_3326,A_3327] :
      ( B_3325 = '#skF_6'
      | v1_partfun1(C_3326,A_3327)
      | ~ v1_funct_2(C_3326,A_3327,B_3325)
      | ~ m1_subset_1(C_3326,k1_zfmisc_1(k2_zfmisc_1(A_3327,B_3325)))
      | ~ v1_funct_1(C_3326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_68])).

tff(c_43020,plain,(
    ! [B_3325,A_3327] :
      ( B_3325 = '#skF_6'
      | v1_partfun1('#skF_6',A_3327)
      | ~ v1_funct_2('#skF_6',A_3327,B_3325)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42271,c_43013])).

tff(c_53229,plain,(
    ! [B_4010,A_4011] :
      ( B_4010 = '#skF_6'
      | v1_partfun1('#skF_6',A_4011)
      | ~ v1_funct_2('#skF_6',A_4011,B_4010) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_43020])).

tff(c_53247,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_117,c_53229])).

tff(c_53286,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_53247])).

tff(c_42264,plain,(
    k6_partfun1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_34031])).

tff(c_42417,plain,(
    ! [C_3227,A_3228,B_3229] :
      ( v4_relat_1(C_3227,A_3228)
      | ~ m1_subset_1(C_3227,k1_zfmisc_1(k2_zfmisc_1(A_3228,B_3229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_42438,plain,(
    ! [A_43] : v4_relat_1(k6_partfun1(A_43),A_43) ),
    inference(resolution,[status(thm)],[c_50,c_42417])).

tff(c_42616,plain,(
    ! [B_3263,A_3264] :
      ( k1_relat_1(B_3263) = A_3264
      | ~ v1_partfun1(B_3263,A_3264)
      | ~ v4_relat_1(B_3263,A_3264)
      | ~ v1_relat_1(B_3263) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42619,plain,(
    ! [A_43] :
      ( k1_relat_1(k6_partfun1(A_43)) = A_43
      | ~ v1_partfun1(k6_partfun1(A_43),A_43)
      | ~ v1_relat_1(k6_partfun1(A_43)) ) ),
    inference(resolution,[status(thm)],[c_42438,c_42616])).

tff(c_42635,plain,(
    ! [A_3265] : k1_relat_1(k6_partfun1(A_3265)) = A_3265 ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_48,c_42619])).

tff(c_42647,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_42264,c_42635])).

tff(c_42260,plain,(
    ! [A_2487] : v4_relat_1('#skF_6',A_2487) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_34087])).

tff(c_42622,plain,(
    ! [A_2487] :
      ( k1_relat_1('#skF_6') = A_2487
      | ~ v1_partfun1('#skF_6',A_2487)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_42260,c_42616])).

tff(c_42631,plain,(
    ! [A_2487] :
      ( k1_relat_1('#skF_6') = A_2487
      | ~ v1_partfun1('#skF_6',A_2487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_42622])).

tff(c_42663,plain,(
    ! [A_2487] :
      ( A_2487 = '#skF_6'
      | ~ v1_partfun1('#skF_6',A_2487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42647,c_42631])).

tff(c_53290,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_53286,c_42663])).

tff(c_53293,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53290,c_33993])).

tff(c_34107,plain,(
    ! [A_2490,B_2491] : ~ r2_hidden(A_2490,'#skF_2'(k1_xboole_0,B_2491)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_243])).

tff(c_34119,plain,(
    ! [B_2492] : '#skF_2'(k1_xboole_0,B_2492) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_34107])).

tff(c_34130,plain,(
    ! [B_2492] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_2492) ),
    inference(superposition,[status(thm),theory(equality)],[c_34119,c_52])).

tff(c_42257,plain,(
    ! [B_2492] : v1_funct_2('#skF_6','#skF_6',B_2492) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_34130])).

tff(c_34115,plain,(
    ! [B_2491] : '#skF_2'(k1_xboole_0,B_2491) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_34107])).

tff(c_42258,plain,(
    ! [B_2491] : '#skF_2'('#skF_6',B_2491) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_34115])).

tff(c_43147,plain,(
    ! [B_3335,A_3336] :
      ( B_3335 = '#skF_6'
      | v1_partfun1('#skF_6',A_3336)
      | ~ v1_funct_2('#skF_6',A_3336,B_3335) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_43020])).

tff(c_43165,plain,
    ( u1_struct_0('#skF_4') = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_117,c_43147])).

tff(c_43166,plain,(
    v1_partfun1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_43165])).

tff(c_43208,plain,(
    u1_struct_0('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_43166,c_42663])).

tff(c_44926,plain,(
    ! [D_3453,A_3454,B_3455] :
      ( v5_pre_topc(D_3453,A_3454,g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))
      | ~ v5_pre_topc(D_3453,A_3454,B_3455)
      | ~ m1_subset_1(D_3453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455))))))
      | ~ v1_funct_2(D_3453,u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455))))
      | ~ m1_subset_1(D_3453,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3454),u1_struct_0(B_3455))))
      | ~ v1_funct_2(D_3453,u1_struct_0(A_3454),u1_struct_0(B_3455))
      | ~ v1_funct_1(D_3453)
      | ~ l1_pre_topc(B_3455)
      | ~ v2_pre_topc(B_3455)
      | ~ l1_pre_topc(A_3454)
      | ~ v2_pre_topc(A_3454) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_44950,plain,(
    ! [A_3454,B_3455] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))),A_3454,g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))),A_3454,B_3455)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))),u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3454),u1_struct_0(B_3455))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))),u1_struct_0(A_3454),u1_struct_0(B_3455))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_3454),u1_struct_0(g1_pre_topc(u1_struct_0(B_3455),u1_pre_topc(B_3455)))))
      | ~ l1_pre_topc(B_3455)
      | ~ v2_pre_topc(B_3455)
      | ~ l1_pre_topc(A_3454)
      | ~ v2_pre_topc(A_3454) ) ),
    inference(resolution,[status(thm)],[c_62,c_44926])).

tff(c_45438,plain,(
    ! [A_3508,B_3509] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_3508),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),A_3508,g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_3508),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),A_3508,B_3509)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_3508),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3508),u1_struct_0(B_3509))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_3508),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),u1_struct_0(A_3508),u1_struct_0(B_3509))
      | ~ l1_pre_topc(B_3509)
      | ~ v2_pre_topc(B_3509)
      | ~ l1_pre_topc(A_3508)
      | ~ v2_pre_topc(A_3508) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_44950])).

tff(c_45448,plain,(
    ! [B_3509] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),'#skF_3',g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),'#skF_3',B_3509)
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_3509))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3509),u1_pre_topc(B_3509)))),u1_struct_0('#skF_3'),u1_struct_0(B_3509))
      | ~ l1_pre_topc(B_3509)
      | ~ v2_pre_topc(B_3509)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43208,c_45438])).

tff(c_46362,plain,(
    ! [B_3584] :
      ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_3584),u1_pre_topc(B_3584)))
      | ~ v5_pre_topc('#skF_6','#skF_3',B_3584)
      | ~ l1_pre_topc(B_3584)
      | ~ v2_pre_topc(B_3584) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_42257,c_42258,c_43208,c_43208,c_42271,c_42258,c_43208,c_42258,c_43208,c_42258,c_43208,c_45448])).

tff(c_42269,plain,(
    ! [B_4] : k2_zfmisc_1('#skF_6',B_4) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_14])).

tff(c_42247,plain,(
    v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitRight,[status(thm)],[c_268])).

tff(c_42268,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_1'(A_24),A_24)
      | A_24 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_34])).

tff(c_42584,plain,(
    ! [A_3256,B_3257,A_3258] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_3256,B_3257))
      | ~ r2_hidden(A_3258,'#skF_2'(A_3256,B_3257)) ) ),
    inference(resolution,[status(thm)],[c_62,c_239])).

tff(c_42600,plain,(
    ! [A_3259,B_3260] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_3259,B_3260))
      | '#skF_2'(A_3259,B_3260) = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_42268,c_42584])).

tff(c_42610,plain,(
    '#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42247,c_42600])).

tff(c_43029,plain,(
    ! [B_45,A_44] :
      ( B_45 = '#skF_6'
      | v1_partfun1('#skF_2'(A_44,B_45),A_44)
      | ~ v1_funct_2('#skF_2'(A_44,B_45),A_44,B_45)
      | ~ v1_funct_1('#skF_2'(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_62,c_43013])).

tff(c_43043,plain,(
    ! [B_3328,A_3329] :
      ( B_3328 = '#skF_6'
      | v1_partfun1('#skF_2'(A_3329,B_3328),A_3329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_43029])).

tff(c_43049,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6'
    | v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_42610,c_43043])).

tff(c_43077,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_43049])).

tff(c_43110,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_43077,c_42663])).

tff(c_43210,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43208,c_43110])).

tff(c_44986,plain,(
    ! [D_3459,A_3460,B_3461] :
      ( v5_pre_topc(D_3459,g1_pre_topc(u1_struct_0(A_3460),u1_pre_topc(A_3460)),B_3461)
      | ~ v5_pre_topc(D_3459,A_3460,B_3461)
      | ~ m1_subset_1(D_3459,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3460),u1_pre_topc(A_3460))),u1_struct_0(B_3461))))
      | ~ v1_funct_2(D_3459,u1_struct_0(g1_pre_topc(u1_struct_0(A_3460),u1_pre_topc(A_3460))),u1_struct_0(B_3461))
      | ~ m1_subset_1(D_3459,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3460),u1_struct_0(B_3461))))
      | ~ v1_funct_2(D_3459,u1_struct_0(A_3460),u1_struct_0(B_3461))
      | ~ v1_funct_1(D_3459)
      | ~ l1_pre_topc(B_3461)
      | ~ v2_pre_topc(B_3461)
      | ~ l1_pre_topc(A_3460)
      | ~ v2_pre_topc(A_3460) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_44995,plain,(
    ! [D_3459,B_3461] :
      ( v5_pre_topc(D_3459,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),B_3461)
      | ~ v5_pre_topc(D_3459,'#skF_3',B_3461)
      | ~ m1_subset_1(D_3459,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_3'))),u1_struct_0(B_3461))))
      | ~ v1_funct_2(D_3459,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),u1_struct_0(B_3461))
      | ~ m1_subset_1(D_3459,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_3461))))
      | ~ v1_funct_2(D_3459,u1_struct_0('#skF_3'),u1_struct_0(B_3461))
      | ~ v1_funct_1(D_3459)
      | ~ l1_pre_topc(B_3461)
      | ~ v2_pre_topc(B_3461)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43208,c_44986])).

tff(c_45244,plain,(
    ! [D_3481,B_3482] :
      ( v5_pre_topc(D_3481,g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),B_3482)
      | ~ v5_pre_topc(D_3481,'#skF_3',B_3482)
      | ~ m1_subset_1(D_3481,k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2(D_3481,'#skF_6',u1_struct_0(B_3482))
      | ~ v1_funct_1(D_3481)
      | ~ l1_pre_topc(B_3482)
      | ~ v2_pre_topc(B_3482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_43208,c_42269,c_43208,c_43210,c_43208,c_42269,c_43210,c_43208,c_44995])).

tff(c_43211,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43208,c_33993])).

tff(c_45251,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_45244,c_43211])).

tff(c_45257,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_42257,c_42271,c_45251])).

tff(c_45384,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_45257])).

tff(c_45387,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_45384])).

tff(c_45391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_45387])).

tff(c_45392,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_45257])).

tff(c_45510,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_45392])).

tff(c_46368,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_46362,c_45510])).

tff(c_46382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_33994,c_46368])).

tff(c_46383,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_45392])).

tff(c_46387,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34171,c_46383])).

tff(c_46391,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_46387])).

tff(c_46392,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_43165])).

tff(c_46394,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46392,c_33993])).

tff(c_43135,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43110,c_34171])).

tff(c_51089,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_43135])).

tff(c_51092,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34171,c_51089])).

tff(c_51096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_51092])).

tff(c_51098,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_43135])).

tff(c_43141,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_6')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43110,c_74])).

tff(c_51268,plain,(
    m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51098,c_43141])).

tff(c_51341,plain,(
    ! [A_3929] :
      ( m1_subset_1(A_3929,k1_zfmisc_1('#skF_6'))
      | ~ r2_hidden(A_3929,u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))) ) ),
    inference(resolution,[status(thm)],[c_51268,c_18])).

tff(c_51346,plain,
    ( m1_subset_1('#skF_1'(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))),k1_zfmisc_1('#skF_6'))
    | u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42268,c_51341])).

tff(c_51788,plain,(
    u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_51346])).

tff(c_51892,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_6'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_51788,c_76])).

tff(c_51965,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6','#skF_6'))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51098,c_43110,c_51892])).

tff(c_51969,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_51965])).

tff(c_51972,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_51969])).

tff(c_51976,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_51972])).

tff(c_51978,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_51965])).

tff(c_46435,plain,(
    ! [D_3585,A_3586,B_3587] :
      ( v5_pre_topc(D_3585,g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586)),B_3587)
      | ~ v5_pre_topc(D_3585,A_3586,B_3587)
      | ~ m1_subset_1(D_3585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587))))
      | ~ v1_funct_2(D_3585,u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587))
      | ~ m1_subset_1(D_3585,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3586),u1_struct_0(B_3587))))
      | ~ v1_funct_2(D_3585,u1_struct_0(A_3586),u1_struct_0(B_3587))
      | ~ v1_funct_1(D_3585)
      | ~ l1_pre_topc(B_3587)
      | ~ v2_pre_topc(B_3587)
      | ~ l1_pre_topc(A_3586)
      | ~ v2_pre_topc(A_3586) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_46462,plain,(
    ! [A_3586,B_3587] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587)),g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586)),B_3587)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587)),A_3586,B_3587)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587)),u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3586),u1_struct_0(B_3587))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587)),u1_struct_0(A_3586),u1_struct_0(B_3587))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586),u1_pre_topc(A_3586))),u1_struct_0(B_3587)))
      | ~ l1_pre_topc(B_3587)
      | ~ v2_pre_topc(B_3587)
      | ~ l1_pre_topc(A_3586)
      | ~ v2_pre_topc(A_3586) ) ),
    inference(resolution,[status(thm)],[c_62,c_46435])).

tff(c_50789,plain,(
    ! [A_3879,B_3880] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0(B_3880)),g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879)),B_3880)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0(B_3880)),A_3879,B_3880)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0(B_3880)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3879),u1_struct_0(B_3880))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0(B_3880)),u1_struct_0(A_3879),u1_struct_0(B_3880))
      | ~ l1_pre_topc(B_3880)
      | ~ v2_pre_topc(B_3880)
      | ~ l1_pre_topc(A_3879)
      | ~ v2_pre_topc(A_3879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_46462])).

tff(c_50799,plain,(
    ! [A_3879] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0('#skF_4')),g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879)),'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0('#skF_4')),A_3879,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3879),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879))),u1_struct_0('#skF_4')),u1_struct_0(A_3879),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_3879)
      | ~ v2_pre_topc(A_3879) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46392,c_50789])).

tff(c_50819,plain,(
    ! [A_3879] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_3879),u1_pre_topc(A_3879)),'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_3879,'#skF_4')
      | ~ l1_pre_topc(A_3879)
      | ~ v2_pre_topc(A_3879) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_42397,c_42261,c_46392,c_46392,c_42271,c_42261,c_46392,c_42261,c_46392,c_42261,c_46392,c_50799])).

tff(c_51841,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))),'#skF_6'),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_51788,c_50819])).

tff(c_51927,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6','#skF_6'),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51098,c_43110,c_51841])).

tff(c_52480,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6','#skF_6'),'#skF_4')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51978,c_51927])).

tff(c_52481,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_52480])).

tff(c_52484,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50819,c_52481])).

tff(c_52488,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_33994,c_52484])).

tff(c_52490,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_52480])).

tff(c_42272,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42253,c_42253,c_12])).

tff(c_49976,plain,(
    ! [D_3798,A_3799,B_3800] :
      ( v5_pre_topc(D_3798,A_3799,g1_pre_topc(u1_struct_0(B_3800),u1_pre_topc(B_3800)))
      | ~ v5_pre_topc(D_3798,A_3799,B_3800)
      | ~ m1_subset_1(D_3798,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799),u1_struct_0(g1_pre_topc(u1_struct_0(B_3800),u1_pre_topc(B_3800))))))
      | ~ v1_funct_2(D_3798,u1_struct_0(A_3799),u1_struct_0(g1_pre_topc(u1_struct_0(B_3800),u1_pre_topc(B_3800))))
      | ~ m1_subset_1(D_3798,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799),u1_struct_0(B_3800))))
      | ~ v1_funct_2(D_3798,u1_struct_0(A_3799),u1_struct_0(B_3800))
      | ~ v1_funct_1(D_3798)
      | ~ l1_pre_topc(B_3800)
      | ~ v2_pre_topc(B_3800)
      | ~ l1_pre_topc(A_3799)
      | ~ v2_pre_topc(A_3799) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_49982,plain,(
    ! [D_3798,A_3799] :
      ( v5_pre_topc(D_3798,A_3799,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc(D_3798,A_3799,'#skF_4')
      | ~ m1_subset_1(D_3798,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2(D_3798,u1_struct_0(A_3799),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(D_3798,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2(D_3798,u1_struct_0(A_3799),u1_struct_0('#skF_4'))
      | ~ v1_funct_1(D_3798)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_3799)
      | ~ v2_pre_topc(A_3799) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46392,c_49976])).

tff(c_53098,plain,(
    ! [D_4005,A_4006] :
      ( v5_pre_topc(D_4005,A_4006,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc(D_4005,A_4006,'#skF_4')
      | ~ m1_subset_1(D_4005,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4006),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))))
      | ~ v1_funct_2(D_4005,u1_struct_0(A_4006),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1(D_4005,k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2(D_4005,u1_struct_0(A_4006),'#skF_6')
      | ~ v1_funct_1(D_4005)
      | ~ l1_pre_topc(A_4006)
      | ~ v2_pre_topc(A_4006) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_46392,c_42272,c_46392,c_46392,c_46392,c_49982])).

tff(c_53120,plain,(
    ! [A_4006] :
      ( v5_pre_topc('#skF_6',A_4006,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_4006,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_4006),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_4006),'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc(A_4006)
      | ~ v2_pre_topc(A_4006) ) ),
    inference(resolution,[status(thm)],[c_42271,c_53098])).

tff(c_53147,plain,(
    ! [A_4007] :
      ( v5_pre_topc('#skF_6',A_4007,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_4007,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_4007),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(A_4007)
      | ~ v2_pre_topc(A_4007) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_42397,c_42271,c_53120])).

tff(c_53153,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ v1_funct_2('#skF_6','#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_43110,c_53147])).

tff(c_53161,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51978,c_51098,c_42257,c_52490,c_53153])).

tff(c_53163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46394,c_53161])).

tff(c_53164,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_43049])).

tff(c_57373,plain,(
    ! [D_4242,A_4243,B_4244] :
      ( v5_pre_topc(D_4242,A_4243,g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))
      | ~ v5_pre_topc(D_4242,A_4243,B_4244)
      | ~ m1_subset_1(D_4242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244))))))
      | ~ v1_funct_2(D_4242,u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244))))
      | ~ m1_subset_1(D_4242,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4243),u1_struct_0(B_4244))))
      | ~ v1_funct_2(D_4242,u1_struct_0(A_4243),u1_struct_0(B_4244))
      | ~ v1_funct_1(D_4242)
      | ~ l1_pre_topc(B_4244)
      | ~ v2_pre_topc(B_4244)
      | ~ l1_pre_topc(A_4243)
      | ~ v2_pre_topc(A_4243) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_57400,plain,(
    ! [A_4243,B_4244] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))),A_4243,g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))),A_4243,B_4244)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))),u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4243),u1_struct_0(B_4244))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))),u1_struct_0(A_4243),u1_struct_0(B_4244))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_4243),u1_struct_0(g1_pre_topc(u1_struct_0(B_4244),u1_pre_topc(B_4244)))))
      | ~ l1_pre_topc(B_4244)
      | ~ v2_pre_topc(B_4244)
      | ~ l1_pre_topc(A_4243)
      | ~ v2_pre_topc(A_4243) ) ),
    inference(resolution,[status(thm)],[c_62,c_57373])).

tff(c_57857,plain,(
    ! [A_4291,B_4292] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),A_4291,g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),A_4291,B_4292)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4291),u1_struct_0(B_4292))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),u1_struct_0(A_4291),u1_struct_0(B_4292))
      | ~ l1_pre_topc(B_4292)
      | ~ v2_pre_topc(B_4292)
      | ~ l1_pre_topc(A_4291)
      | ~ v2_pre_topc(A_4291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_57400])).

tff(c_57871,plain,(
    ! [A_4291] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_4291,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_4291,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4291),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4291),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4291),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_4291),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_4291)
      | ~ v2_pre_topc(A_4291) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53164,c_57857])).

tff(c_57889,plain,(
    ! [A_4291] :
      ( v5_pre_topc('#skF_6',A_4291,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_4291,'#skF_4')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_4291),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc(A_4291)
      | ~ v2_pre_topc(A_4291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_42261,c_53164,c_42271,c_42261,c_42261,c_53164,c_42261,c_53164,c_57871])).

tff(c_42305,plain,(
    ! [A_3219,B_3220] :
      ( v1_pre_topc(g1_pre_topc(A_3219,B_3220))
      | ~ m1_subset_1(B_3220,k1_zfmisc_1(k1_zfmisc_1(A_3219))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_42309,plain,(
    ! [A_53] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_53),u1_pre_topc(A_53)))
      | ~ l1_pre_topc(A_53) ) ),
    inference(resolution,[status(thm)],[c_74,c_42305])).

tff(c_53214,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53164,c_42309])).

tff(c_57445,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_53214])).

tff(c_57448,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_34171,c_57445])).

tff(c_57452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_57448])).

tff(c_57454,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_53214])).

tff(c_53220,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53164,c_76])).

tff(c_60580,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57454,c_53220])).

tff(c_60581,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_60580])).

tff(c_60584,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_60581])).

tff(c_60588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_60584])).

tff(c_60590,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_60580])).

tff(c_57281,plain,(
    ! [D_4235,A_4236,B_4237] :
      ( v5_pre_topc(D_4235,A_4236,B_4237)
      | ~ v5_pre_topc(D_4235,A_4236,g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))
      | ~ m1_subset_1(D_4235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237))))))
      | ~ v1_funct_2(D_4235,u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237))))
      | ~ m1_subset_1(D_4235,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4236),u1_struct_0(B_4237))))
      | ~ v1_funct_2(D_4235,u1_struct_0(A_4236),u1_struct_0(B_4237))
      | ~ v1_funct_1(D_4235)
      | ~ l1_pre_topc(B_4237)
      | ~ v2_pre_topc(B_4237)
      | ~ l1_pre_topc(A_4236)
      | ~ v2_pre_topc(A_4236) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_57308,plain,(
    ! [A_4236,B_4237] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))),A_4236,B_4237)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))),A_4236,g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))),u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4236),u1_struct_0(B_4237))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))),u1_struct_0(A_4236),u1_struct_0(B_4237))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_4236),u1_struct_0(g1_pre_topc(u1_struct_0(B_4237),u1_pre_topc(B_4237)))))
      | ~ l1_pre_topc(B_4237)
      | ~ v2_pre_topc(B_4237)
      | ~ l1_pre_topc(A_4236)
      | ~ v2_pre_topc(A_4236) ) ),
    inference(resolution,[status(thm)],[c_62,c_57281])).

tff(c_58140,plain,(
    ! [A_4325,B_4326] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4325),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),A_4325,B_4326)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4325),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),A_4325,g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4325),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4325),u1_struct_0(B_4326))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4325),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),u1_struct_0(A_4325),u1_struct_0(B_4326))
      | ~ l1_pre_topc(B_4326)
      | ~ v2_pre_topc(B_4326)
      | ~ l1_pre_topc(A_4325)
      | ~ v2_pre_topc(A_4325) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_57308])).

tff(c_58142,plain,(
    ! [B_4326] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),'#skF_3',B_4326)
      | ~ v5_pre_topc('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),'#skF_3',g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_4326))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4326),u1_pre_topc(B_4326)))),u1_struct_0('#skF_3'),u1_struct_0(B_4326))
      | ~ l1_pre_topc(B_4326)
      | ~ v2_pre_topc(B_4326)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53290,c_58140])).

tff(c_58462,plain,(
    ! [B_4360] :
      ( v5_pre_topc('#skF_6','#skF_3',B_4360)
      | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_4360),u1_pre_topc(B_4360)))
      | ~ l1_pre_topc(B_4360)
      | ~ v2_pre_topc(B_4360) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_42257,c_42258,c_53290,c_53290,c_42271,c_42258,c_53290,c_53290,c_42258,c_42258,c_53290,c_58142])).

tff(c_58471,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53164,c_58462])).

tff(c_58477,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57454,c_58471])).

tff(c_61379,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60590,c_58477])).

tff(c_61380,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))) ),
    inference(splitLeft,[status(thm)],[c_61379])).

tff(c_57859,plain,(
    ! [B_4292] :
      ( v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),'#skF_3',g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),'#skF_3',B_4292)
      | ~ m1_subset_1('#skF_2'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_4292))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0('#skF_3'),u1_struct_0(g1_pre_topc(u1_struct_0(B_4292),u1_pre_topc(B_4292)))),u1_struct_0('#skF_3'),u1_struct_0(B_4292))
      | ~ l1_pre_topc(B_4292)
      | ~ v2_pre_topc(B_4292)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53290,c_57857])).

tff(c_57934,plain,(
    ! [B_4298] :
      ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0(B_4298),u1_pre_topc(B_4298)))
      | ~ v5_pre_topc('#skF_6','#skF_3',B_4298)
      | ~ l1_pre_topc(B_4298)
      | ~ v2_pre_topc(B_4298) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_42257,c_42258,c_53290,c_53290,c_42271,c_42258,c_53290,c_42258,c_53290,c_42258,c_53290,c_57859])).

tff(c_57940,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_53164,c_57934])).

tff(c_57944,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57454,c_57940])).

tff(c_61382,plain,
    ( v5_pre_topc('#skF_6','#skF_3',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60590,c_57944])).

tff(c_61383,plain,(
    ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_61380,c_61382])).

tff(c_61386,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_57889,c_61383])).

tff(c_61393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_42257,c_53290,c_33994,c_61386])).

tff(c_61394,plain,(
    v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_61379])).

tff(c_42880,plain,(
    ! [D_3312,B_3313,C_3314,A_3315] :
      ( m1_subset_1(D_3312,k1_zfmisc_1(k2_zfmisc_1(B_3313,C_3314)))
      | ~ r1_tarski(k1_relat_1(D_3312),B_3313)
      | ~ m1_subset_1(D_3312,k1_zfmisc_1(k2_zfmisc_1(A_3315,C_3314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42895,plain,(
    ! [A_44,B_45,B_3313] :
      ( m1_subset_1('#skF_2'(A_44,B_45),k1_zfmisc_1(k2_zfmisc_1(B_3313,B_45)))
      | ~ r1_tarski(k1_relat_1('#skF_2'(A_44,B_45)),B_3313) ) ),
    inference(resolution,[status(thm)],[c_62,c_42880])).

tff(c_53248,plain,(
    ! [D_4012,A_4013,B_4014] :
      ( v5_pre_topc(D_4012,g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013)),B_4014)
      | ~ v5_pre_topc(D_4012,A_4013,B_4014)
      | ~ m1_subset_1(D_4012,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014))))
      | ~ v1_funct_2(D_4012,u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014))
      | ~ m1_subset_1(D_4012,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4013),u1_struct_0(B_4014))))
      | ~ v1_funct_2(D_4012,u1_struct_0(A_4013),u1_struct_0(B_4014))
      | ~ v1_funct_1(D_4012)
      | ~ l1_pre_topc(B_4014)
      | ~ v2_pre_topc(B_4014)
      | ~ l1_pre_topc(A_4013)
      | ~ v2_pre_topc(A_4013) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_53269,plain,(
    ! [A_4013,B_4014] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014)),g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013)),B_4014)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014)),A_4013,B_4014)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014)),u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4013),u1_struct_0(B_4014))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014)),u1_struct_0(A_4013),u1_struct_0(B_4014))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013),u1_pre_topc(A_4013))),u1_struct_0(B_4014)))
      | ~ l1_pre_topc(B_4014)
      | ~ v2_pre_topc(B_4014)
      | ~ l1_pre_topc(A_4013)
      | ~ v2_pre_topc(A_4013) ) ),
    inference(resolution,[status(thm)],[c_62,c_53248])).

tff(c_57675,plain,(
    ! [A_4270,B_4271] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270),u1_pre_topc(A_4270))),u1_struct_0(B_4271)),g1_pre_topc(u1_struct_0(A_4270),u1_pre_topc(A_4270)),B_4271)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270),u1_pre_topc(A_4270))),u1_struct_0(B_4271)),A_4270,B_4271)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270),u1_pre_topc(A_4270))),u1_struct_0(B_4271)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4270),u1_struct_0(B_4271))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270),u1_pre_topc(A_4270))),u1_struct_0(B_4271)),u1_struct_0(A_4270),u1_struct_0(B_4271))
      | ~ l1_pre_topc(B_4271)
      | ~ v2_pre_topc(B_4271)
      | ~ l1_pre_topc(A_4270)
      | ~ v2_pre_topc(A_4270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_53269])).

tff(c_60593,plain,(
    ! [A_4446,B_4447] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(B_4447)),g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446)),B_4447)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(B_4447)),A_4446,B_4447)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(B_4447)),u1_struct_0(A_4446),u1_struct_0(B_4447))
      | ~ l1_pre_topc(B_4447)
      | ~ v2_pre_topc(B_4447)
      | ~ l1_pre_topc(A_4446)
      | ~ v2_pre_topc(A_4446)
      | ~ r1_tarski(k1_relat_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(B_4447))),u1_struct_0(A_4446)) ) ),
    inference(resolution,[status(thm)],[c_42895,c_57675])).

tff(c_60616,plain,(
    ! [A_4446] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),'#skF_6'),g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_4446,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_4446),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_4446)
      | ~ v2_pre_topc(A_4446)
      | ~ r1_tarski(k1_relat_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446),u1_pre_topc(A_4446))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))),u1_struct_0(A_4446)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53164,c_60593])).

tff(c_62084,plain,(
    ! [A_4507] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_4507),u1_pre_topc(A_4507)),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_4507,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_4507)
      | ~ v2_pre_topc(A_4507)
      | ~ r1_tarski('#skF_6',u1_struct_0(A_4507)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42647,c_42261,c_53164,c_60590,c_57454,c_42397,c_42261,c_53164,c_53164,c_42261,c_53164,c_42261,c_60616])).

tff(c_62097,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v5_pre_topc('#skF_6','#skF_3',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_53290,c_62084])).

tff(c_62110,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_53290,c_108,c_106,c_61394,c_62097])).

tff(c_62112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53293,c_62110])).

tff(c_62113,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_53247])).

tff(c_64649,plain,(
    ! [A_4711,B_4712] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0(B_4712)),g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711)),B_4712)
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0(B_4712)),A_4711,B_4712)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0(B_4712)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4711),u1_struct_0(B_4712))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0(B_4712)),u1_struct_0(A_4711),u1_struct_0(B_4712))
      | ~ l1_pre_topc(B_4712)
      | ~ v2_pre_topc(B_4712)
      | ~ l1_pre_topc(A_4711)
      | ~ v2_pre_topc(A_4711) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_53269])).

tff(c_64664,plain,(
    ! [A_4711] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0('#skF_4')),g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711)),'#skF_4')
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0('#skF_4')),A_4711,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4711),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711),u1_pre_topc(A_4711))),u1_struct_0('#skF_4')),u1_struct_0(A_4711),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_4711)
      | ~ v2_pre_topc(A_4711) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62113,c_64649])).

tff(c_65479,plain,(
    ! [A_4776] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_4776),u1_pre_topc(A_4776)),'#skF_4')
      | ~ v5_pre_topc('#skF_6',A_4776,'#skF_4')
      | ~ l1_pre_topc(A_4776)
      | ~ v2_pre_topc(A_4776) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_42397,c_42261,c_62113,c_62113,c_42271,c_42261,c_62113,c_42261,c_62113,c_42261,c_62113,c_64664])).

tff(c_62115,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62113,c_53164])).

tff(c_64109,plain,(
    ! [D_4652,A_4653,B_4654] :
      ( v5_pre_topc(D_4652,A_4653,g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))
      | ~ v5_pre_topc(D_4652,A_4653,B_4654)
      | ~ m1_subset_1(D_4652,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654))))))
      | ~ v1_funct_2(D_4652,u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654))))
      | ~ m1_subset_1(D_4652,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4653),u1_struct_0(B_4654))))
      | ~ v1_funct_2(D_4652,u1_struct_0(A_4653),u1_struct_0(B_4654))
      | ~ v1_funct_1(D_4652)
      | ~ l1_pre_topc(B_4654)
      | ~ v2_pre_topc(B_4654)
      | ~ l1_pre_topc(A_4653)
      | ~ v2_pre_topc(A_4653) ) ),
    inference(cnfTransformation,[status(thm)],[f_221])).

tff(c_64133,plain,(
    ! [A_4653,B_4654] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))),A_4653,g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))),A_4653,B_4654)
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))),u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654))))
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4653),u1_struct_0(B_4654))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))),u1_struct_0(A_4653),u1_struct_0(B_4654))
      | ~ v1_funct_1('#skF_2'(u1_struct_0(A_4653),u1_struct_0(g1_pre_topc(u1_struct_0(B_4654),u1_pre_topc(B_4654)))))
      | ~ l1_pre_topc(B_4654)
      | ~ v2_pre_topc(B_4654)
      | ~ l1_pre_topc(A_4653)
      | ~ v2_pre_topc(A_4653) ) ),
    inference(resolution,[status(thm)],[c_62,c_64109])).

tff(c_64400,plain,(
    ! [A_4680,B_4681] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0(B_4681),u1_pre_topc(B_4681)))),A_4680,g1_pre_topc(u1_struct_0(B_4681),u1_pre_topc(B_4681)))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0(B_4681),u1_pre_topc(B_4681)))),A_4680,B_4681)
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0(B_4681),u1_pre_topc(B_4681)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4680),u1_struct_0(B_4681))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0(B_4681),u1_pre_topc(B_4681)))),u1_struct_0(A_4680),u1_struct_0(B_4681))
      | ~ l1_pre_topc(B_4681)
      | ~ v2_pre_topc(B_4681)
      | ~ l1_pre_topc(A_4680)
      | ~ v2_pre_topc(A_4680) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_64133])).

tff(c_64412,plain,(
    ! [A_4680] :
      ( v5_pre_topc('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_4680,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),A_4680,'#skF_4')
      | ~ m1_subset_1('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4680),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_2'(u1_struct_0(A_4680),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))),u1_struct_0(A_4680),u1_struct_0('#skF_4'))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_4680)
      | ~ v2_pre_topc(A_4680) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62113,c_64400])).

tff(c_64440,plain,(
    ! [A_4684] :
      ( v5_pre_topc('#skF_6',A_4684,g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')))
      | ~ v5_pre_topc('#skF_6',A_4684,'#skF_4')
      | ~ l1_pre_topc(A_4684)
      | ~ v2_pre_topc(A_4684) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_42397,c_42261,c_62113,c_62115,c_62113,c_42271,c_42261,c_62113,c_62115,c_42261,c_62115,c_62113,c_42261,c_62113,c_62115,c_62113,c_64412])).

tff(c_62116,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62113,c_33993])).

tff(c_64450,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_64440,c_62116])).

tff(c_64608,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_64450])).

tff(c_64611,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_64608])).

tff(c_64615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_64611])).

tff(c_64616,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_64450])).

tff(c_64771,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64616])).

tff(c_65485,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_65479,c_64771])).

tff(c_65499,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_106,c_33994,c_65485])).

tff(c_65500,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_64616])).

tff(c_65505,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_34171,c_65500])).

tff(c_65509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_65505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:55:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.60/12.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.01/13.11  
% 22.01/13.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.01/13.12  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_mcart_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 22.01/13.12  
% 22.01/13.12  %Foreground sorts:
% 22.01/13.12  
% 22.01/13.12  
% 22.01/13.12  %Background operators:
% 22.01/13.12  
% 22.01/13.12  
% 22.01/13.12  %Foreground operators:
% 22.01/13.12  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 22.01/13.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 22.01/13.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.01/13.12  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 22.01/13.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.01/13.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 22.01/13.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 22.01/13.12  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 22.01/13.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 22.01/13.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.01/13.12  tff('#skF_5', type, '#skF_5': $i).
% 22.01/13.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 22.01/13.12  tff('#skF_6', type, '#skF_6': $i).
% 22.01/13.12  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 22.01/13.12  tff('#skF_3', type, '#skF_3': $i).
% 22.01/13.12  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 22.01/13.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 22.01/13.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 22.01/13.12  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 22.01/13.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.01/13.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 22.01/13.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 22.01/13.12  tff('#skF_4', type, '#skF_4': $i).
% 22.01/13.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 22.01/13.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.01/13.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 22.01/13.12  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 22.01/13.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 22.01/13.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 22.01/13.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 22.01/13.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 22.01/13.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 22.01/13.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 22.01/13.12  
% 22.01/13.18  tff(f_251, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_pre_topc)).
% 22.01/13.18  tff(f_155, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 22.01/13.18  tff(f_151, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 22.01/13.18  tff(f_163, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 22.01/13.18  tff(f_91, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 22.01/13.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 22.01/13.18  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 22.01/13.18  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.01/13.18  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 22.01/13.18  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 22.01/13.18  tff(f_109, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 22.01/13.18  tff(f_145, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 22.01/13.18  tff(f_53, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 22.01/13.18  tff(f_221, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_pre_topc)).
% 22.01/13.18  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 22.01/13.18  tff(f_192, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_pre_topc)).
% 22.01/13.18  tff(f_113, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 22.01/13.18  tff(f_126, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_funct_2)).
% 22.01/13.18  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 22.01/13.18  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 22.01/13.18  tff(c_106, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_74, plain, (![A_53]: (m1_subset_1(u1_pre_topc(A_53), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_53)))) | ~l1_pre_topc(A_53))), inference(cnfTransformation, [status(thm)], [f_155])).
% 22.01/13.18  tff(c_34163, plain, (![A_2495, B_2496]: (l1_pre_topc(g1_pre_topc(A_2495, B_2496)) | ~m1_subset_1(B_2496, k1_zfmisc_1(k1_zfmisc_1(A_2495))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 22.01/13.18  tff(c_34171, plain, (![A_53]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(A_53))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_74, c_34163])).
% 22.01/13.18  tff(c_108, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_88, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_110, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_120, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_110])).
% 22.01/13.18  tff(c_272, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_120])).
% 22.01/13.18  tff(c_450, plain, (![A_152]: (m1_subset_1(u1_pre_topc(A_152), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_152)))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_155])).
% 22.01/13.18  tff(c_70, plain, (![A_51, B_52]: (l1_pre_topc(g1_pre_topc(A_51, B_52)) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 22.01/13.18  tff(c_456, plain, (![A_152]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_152), u1_pre_topc(A_152))) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_450, c_70])).
% 22.01/13.18  tff(c_76, plain, (![A_54]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_54), u1_pre_topc(A_54))) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54))), inference(cnfTransformation, [status(thm)], [f_163])).
% 22.01/13.18  tff(c_104, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_102, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_98, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_117, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_98])).
% 22.01/13.18  tff(c_94, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_34, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_91])).
% 22.01/13.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 22.01/13.18  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.01/13.18  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.01/13.18  tff(c_96, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_121, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_96])).
% 22.01/13.18  tff(c_212, plain, (![C_123, A_124, B_125]: (v1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 22.01/13.18  tff(c_235, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_121, c_212])).
% 22.01/13.18  tff(c_471, plain, (![C_156, A_157, B_158]: (v4_relat_1(C_156, A_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.01/13.18  tff(c_496, plain, (v4_relat_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_121, c_471])).
% 22.01/13.18  tff(c_637, plain, (![B_201, A_202]: (k1_relat_1(B_201)=A_202 | ~v1_partfun1(B_201, A_202) | ~v4_relat_1(B_201, A_202) | ~v1_relat_1(B_201))), inference(cnfTransformation, [status(thm)], [f_109])).
% 22.01/13.18  tff(c_646, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_496, c_637])).
% 22.01/13.18  tff(c_661, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_646])).
% 22.01/13.18  tff(c_703, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_661])).
% 22.01/13.18  tff(c_971, plain, (![B_243, C_244, A_245]: (k1_xboole_0=B_243 | v1_partfun1(C_244, A_245) | ~v1_funct_2(C_244, A_245, B_243) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_245, B_243))) | ~v1_funct_1(C_244))), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.01/13.18  tff(c_980, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_121, c_971])).
% 22.01/13.18  tff(c_1003, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_117, c_980])).
% 22.01/13.18  tff(c_1004, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_703, c_1003])).
% 22.01/13.18  tff(c_239, plain, (![C_126, B_127, A_128]: (~v1_xboole_0(C_126) | ~m1_subset_1(B_127, k1_zfmisc_1(C_126)) | ~r2_hidden(A_128, B_127))), inference(cnfTransformation, [status(thm)], [f_53])).
% 22.01/13.18  tff(c_263, plain, (![A_128]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))) | ~r2_hidden(A_128, '#skF_6'))), inference(resolution, [status(thm)], [c_121, c_239])).
% 22.01/13.18  tff(c_531, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_263])).
% 22.01/13.18  tff(c_1018, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_1004, c_531])).
% 22.01/13.18  tff(c_1029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_1018])).
% 22.01/13.18  tff(c_1030, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_661])).
% 22.01/13.18  tff(c_92, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_1042, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_92])).
% 22.01/13.18  tff(c_90, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_1041, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_90])).
% 22.01/13.18  tff(c_1436, plain, (![B_276, C_277, A_278]: (k1_xboole_0=B_276 | v1_partfun1(C_277, A_278) | ~v1_funct_2(C_277, A_278, B_276) | ~m1_subset_1(C_277, k1_zfmisc_1(k2_zfmisc_1(A_278, B_276))) | ~v1_funct_1(C_277))), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.01/13.18  tff(c_1445, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_1041, c_1436])).
% 22.01/13.18  tff(c_1471, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_1042, c_1445])).
% 22.01/13.18  tff(c_2176, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_1471])).
% 22.01/13.18  tff(c_498, plain, (v4_relat_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_90, c_471])).
% 22.01/13.18  tff(c_640, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_498, c_637])).
% 22.01/13.18  tff(c_655, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_640])).
% 22.01/13.18  tff(c_2302, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2176, c_1030, c_1030, c_655])).
% 22.01/13.18  tff(c_1040, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_117])).
% 22.01/13.18  tff(c_1039, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_121])).
% 22.01/13.18  tff(c_1048, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_76])).
% 22.01/13.18  tff(c_1063, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_1048])).
% 22.01/13.18  tff(c_1054, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1030, c_456])).
% 22.01/13.18  tff(c_1067, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_1054])).
% 22.01/13.18  tff(c_116, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_4') | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_251])).
% 22.01/13.18  tff(c_118, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_116])).
% 22.01/13.18  tff(c_433, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_272, c_118])).
% 22.01/13.18  tff(c_1038, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_433])).
% 22.01/13.18  tff(c_1812, plain, (![D_322, A_323, B_324]: (v5_pre_topc(D_322, A_323, B_324) | ~v5_pre_topc(D_322, A_323, g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324))) | ~m1_subset_1(D_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_323), u1_struct_0(g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324)))))) | ~v1_funct_2(D_322, u1_struct_0(A_323), u1_struct_0(g1_pre_topc(u1_struct_0(B_324), u1_pre_topc(B_324)))) | ~m1_subset_1(D_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_323), u1_struct_0(B_324)))) | ~v1_funct_2(D_322, u1_struct_0(A_323), u1_struct_0(B_324)) | ~v1_funct_1(D_322) | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | ~l1_pre_topc(A_323) | ~v2_pre_topc(A_323))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.01/13.18  tff(c_1823, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_1041, c_1812])).
% 22.01/13.18  tff(c_1848, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1067, c_104, c_102, c_94, c_1042, c_1038, c_1823])).
% 22.01/13.18  tff(c_2801, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1040, c_2302, c_1039, c_2302, c_1848])).
% 22.01/13.18  tff(c_1245, plain, (![D_258, B_259, C_260, A_261]: (m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(B_259, C_260))) | ~r1_tarski(k1_relat_1(D_258), B_259) | ~m1_subset_1(D_258, k1_zfmisc_1(k2_zfmisc_1(A_261, C_260))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 22.01/13.18  tff(c_1262, plain, (![B_259]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_259, u1_struct_0('#skF_4')))) | ~r1_tarski(k1_relat_1('#skF_6'), B_259))), inference(resolution, [status(thm)], [c_1039, c_1245])).
% 22.01/13.18  tff(c_2037, plain, (![D_345, A_346, B_347]: (v5_pre_topc(D_345, A_346, B_347) | ~v5_pre_topc(D_345, g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346)), B_347) | ~m1_subset_1(D_345, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346))), u1_struct_0(B_347)))) | ~v1_funct_2(D_345, u1_struct_0(g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346))), u1_struct_0(B_347)) | ~m1_subset_1(D_345, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_346), u1_struct_0(B_347)))) | ~v1_funct_2(D_345, u1_struct_0(A_346), u1_struct_0(B_347)) | ~v1_funct_1(D_345) | ~l1_pre_topc(B_347) | ~v2_pre_topc(B_347) | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.01/13.18  tff(c_2049, plain, (![A_346]: (v5_pre_topc('#skF_6', A_346, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346)), '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346))), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_346), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(A_346), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_346) | ~v2_pre_topc(A_346) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_346), u1_pre_topc(A_346)))))), inference(resolution, [status(thm)], [c_1262, c_2037])).
% 22.01/13.18  tff(c_4274, plain, (![A_530]: (v5_pre_topc('#skF_6', A_530, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_530), u1_pre_topc(A_530)), '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_530), u1_pre_topc(A_530))), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_530), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(A_530), u1_struct_0('#skF_4')) | ~l1_pre_topc(A_530) | ~v2_pre_topc(A_530) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_530), u1_pre_topc(A_530)))))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_94, c_2049])).
% 22.01/13.18  tff(c_4286, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_1030, c_4274])).
% 22.01/13.18  tff(c_4293, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2302, c_1030, c_108, c_106, c_1040, c_1030, c_1039, c_1030, c_1040, c_2302, c_2801, c_1030, c_4286])).
% 22.01/13.18  tff(c_4295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_4293])).
% 22.01/13.18  tff(c_4296, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1471])).
% 22.01/13.18  tff(c_268, plain, (![A_128]: (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~r2_hidden(A_128, '#skF_6'))), inference(resolution, [status(thm)], [c_90, c_239])).
% 22.01/13.18  tff(c_470, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitLeft, [status(thm)], [c_268])).
% 22.01/13.18  tff(c_1032, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_470])).
% 22.01/13.18  tff(c_4298, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_4296, c_1032])).
% 22.01/13.18  tff(c_4306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_4298])).
% 22.01/13.18  tff(c_4309, plain, (![A_531]: (~r2_hidden(A_531, '#skF_6'))), inference(splitRight, [status(thm)], [c_263])).
% 22.01/13.18  tff(c_4314, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_34, c_4309])).
% 22.01/13.18  tff(c_4336, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_2])).
% 22.01/13.18  tff(c_4335, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_4314, c_12])).
% 22.01/13.18  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.01/13.18  tff(c_4332, plain, (![B_4]: (k2_zfmisc_1('#skF_6', B_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_4314, c_14])).
% 22.01/13.18  tff(c_175, plain, (![A_114]: (m1_subset_1(k6_partfun1(A_114), k1_zfmisc_1(k2_zfmisc_1(A_114, A_114))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 22.01/13.18  tff(c_179, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_175])).
% 22.01/13.18  tff(c_249, plain, (![A_128]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_128, k6_partfun1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_179, c_239])).
% 22.01/13.18  tff(c_273, plain, (![A_130]: (~r2_hidden(A_130, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_249])).
% 22.01/13.18  tff(c_278, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_273])).
% 22.01/13.18  tff(c_4328, plain, (k6_partfun1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_4314, c_278])).
% 22.01/13.18  tff(c_50, plain, (![A_43]: (m1_subset_1(k6_partfun1(A_43), k1_zfmisc_1(k2_zfmisc_1(A_43, A_43))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 22.01/13.18  tff(c_236, plain, (![A_43]: (v1_relat_1(k6_partfun1(A_43)))), inference(resolution, [status(thm)], [c_50, c_212])).
% 22.01/13.18  tff(c_48, plain, (![A_43]: (v1_partfun1(k6_partfun1(A_43), A_43))), inference(cnfTransformation, [status(thm)], [f_113])).
% 22.01/13.18  tff(c_497, plain, (![A_43]: (v4_relat_1(k6_partfun1(A_43), A_43))), inference(resolution, [status(thm)], [c_50, c_471])).
% 22.01/13.18  tff(c_4597, plain, (![B_550, A_551]: (k1_relat_1(B_550)=A_551 | ~v1_partfun1(B_550, A_551) | ~v4_relat_1(B_550, A_551) | ~v1_relat_1(B_550))), inference(cnfTransformation, [status(thm)], [f_109])).
% 22.01/13.18  tff(c_4603, plain, (![A_43]: (k1_relat_1(k6_partfun1(A_43))=A_43 | ~v1_partfun1(k6_partfun1(A_43), A_43) | ~v1_relat_1(k6_partfun1(A_43)))), inference(resolution, [status(thm)], [c_497, c_4597])).
% 22.01/13.18  tff(c_4616, plain, (![A_552]: (k1_relat_1(k6_partfun1(A_552))=A_552)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_48, c_4603])).
% 22.01/13.18  tff(c_4628, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4328, c_4616])).
% 22.01/13.18  tff(c_4308, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_263])).
% 22.01/13.18  tff(c_4331, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | A_24='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_34])).
% 22.01/13.18  tff(c_62, plain, (![A_44, B_45]: (m1_subset_1('#skF_2'(A_44, B_45), k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 22.01/13.18  tff(c_4692, plain, (![A_570, B_571, A_572]: (~v1_xboole_0(k2_zfmisc_1(A_570, B_571)) | ~r2_hidden(A_572, '#skF_2'(A_570, B_571)))), inference(resolution, [status(thm)], [c_62, c_239])).
% 22.01/13.18  tff(c_4708, plain, (![A_573, B_574]: (~v1_xboole_0(k2_zfmisc_1(A_573, B_574)) | '#skF_2'(A_573, B_574)='#skF_6')), inference(resolution, [status(thm)], [c_4331, c_4692])).
% 22.01/13.18  tff(c_4718, plain, ('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_4308, c_4708])).
% 22.01/13.18  tff(c_54, plain, (![A_44, B_45]: (v1_funct_1('#skF_2'(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 22.01/13.18  tff(c_52, plain, (![A_44, B_45]: (v1_funct_2('#skF_2'(A_44, B_45), A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_126])).
% 22.01/13.18  tff(c_68, plain, (![B_49, C_50, A_48]: (k1_xboole_0=B_49 | v1_partfun1(C_50, A_48) | ~v1_funct_2(C_50, A_48, B_49) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1(C_50))), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.01/13.18  tff(c_4954, plain, (![B_605, C_606, A_607]: (B_605='#skF_6' | v1_partfun1(C_606, A_607) | ~v1_funct_2(C_606, A_607, B_605) | ~m1_subset_1(C_606, k1_zfmisc_1(k2_zfmisc_1(A_607, B_605))) | ~v1_funct_1(C_606))), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_68])).
% 22.01/13.18  tff(c_4970, plain, (![B_45, A_44]: (B_45='#skF_6' | v1_partfun1('#skF_2'(A_44, B_45), A_44) | ~v1_funct_2('#skF_2'(A_44, B_45), A_44, B_45) | ~v1_funct_1('#skF_2'(A_44, B_45)))), inference(resolution, [status(thm)], [c_62, c_4954])).
% 22.01/13.18  tff(c_4984, plain, (![B_608, A_609]: (B_608='#skF_6' | v1_partfun1('#skF_2'(A_609, B_608), A_609))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_4970])).
% 22.01/13.18  tff(c_60, plain, (![A_44, B_45]: (v1_relat_1('#skF_2'(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 22.01/13.18  tff(c_58, plain, (![A_44, B_45]: (v4_relat_1('#skF_2'(A_44, B_45), A_44))), inference(cnfTransformation, [status(thm)], [f_126])).
% 22.01/13.18  tff(c_4606, plain, (![A_44, B_45]: (k1_relat_1('#skF_2'(A_44, B_45))=A_44 | ~v1_partfun1('#skF_2'(A_44, B_45), A_44) | ~v1_relat_1('#skF_2'(A_44, B_45)))), inference(resolution, [status(thm)], [c_58, c_4597])).
% 22.01/13.18  tff(c_4615, plain, (![A_44, B_45]: (k1_relat_1('#skF_2'(A_44, B_45))=A_44 | ~v1_partfun1('#skF_2'(A_44, B_45), A_44))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4606])).
% 22.01/13.18  tff(c_5070, plain, (![A_620, B_621]: (k1_relat_1('#skF_2'(A_620, B_621))=A_620 | B_621='#skF_6')), inference(resolution, [status(thm)], [c_4984, c_4615])).
% 22.01/13.18  tff(c_5082, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | u1_struct_0('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_4718, c_5070])).
% 22.01/13.18  tff(c_5093, plain, (u1_struct_0('#skF_3')='#skF_6' | u1_struct_0('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_4628, c_5082])).
% 22.01/13.18  tff(c_5097, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitLeft, [status(thm)], [c_5093])).
% 22.01/13.18  tff(c_5104, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_5097, c_92])).
% 22.01/13.18  tff(c_16, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 22.01/13.18  tff(c_4334, plain, (![A_5]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_16])).
% 22.01/13.18  tff(c_4961, plain, (![B_605, A_607]: (B_605='#skF_6' | v1_partfun1('#skF_6', A_607) | ~v1_funct_2('#skF_6', A_607, B_605) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_4334, c_4954])).
% 22.01/13.18  tff(c_5206, plain, (![B_626, A_627]: (B_626='#skF_6' | v1_partfun1('#skF_6', A_627) | ~v1_funct_2('#skF_6', A_627, B_626))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4961])).
% 22.01/13.18  tff(c_5219, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_5104, c_5206])).
% 22.01/13.18  tff(c_6005, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_5219])).
% 22.01/13.18  tff(c_203, plain, (![A_119, B_120]: (m1_subset_1('#skF_2'(A_119, B_120), k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 22.01/13.18  tff(c_209, plain, (![A_3]: (m1_subset_1('#skF_2'(A_3, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_203])).
% 22.01/13.18  tff(c_241, plain, (![A_128, A_3]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_128, '#skF_2'(A_3, k1_xboole_0)))), inference(resolution, [status(thm)], [c_209, c_239])).
% 22.01/13.18  tff(c_386, plain, (![A_144, A_145]: (~r2_hidden(A_144, '#skF_2'(A_145, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_241])).
% 22.01/13.18  tff(c_398, plain, (![A_146]: ('#skF_2'(A_146, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_386])).
% 22.01/13.18  tff(c_412, plain, (![A_146]: (v4_relat_1(k1_xboole_0, A_146))), inference(superposition, [status(thm), theory('equality')], [c_398, c_58])).
% 22.01/13.18  tff(c_4320, plain, (![A_146]: (v4_relat_1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_4314, c_412])).
% 22.01/13.18  tff(c_4600, plain, (![A_146]: (k1_relat_1('#skF_6')=A_146 | ~v1_partfun1('#skF_6', A_146) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_4320, c_4597])).
% 22.01/13.18  tff(c_4609, plain, (![A_146]: (k1_relat_1('#skF_6')=A_146 | ~v1_partfun1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_4600])).
% 22.01/13.18  tff(c_4644, plain, (![A_146]: (A_146='#skF_6' | ~v1_partfun1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_4628, c_4609])).
% 22.01/13.18  tff(c_6011, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_6005, c_4644])).
% 22.01/13.18  tff(c_5101, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_5097, c_470])).
% 22.01/13.18  tff(c_6138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4336, c_4332, c_6011, c_5101])).
% 22.01/13.18  tff(c_6139, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_5219])).
% 22.01/13.18  tff(c_6249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4336, c_4335, c_6139, c_5101])).
% 22.01/13.18  tff(c_6250, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_5093])).
% 22.01/13.18  tff(c_6258, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_6250, c_92])).
% 22.01/13.18  tff(c_6361, plain, (![B_695, A_696]: (B_695='#skF_6' | v1_partfun1('#skF_6', A_696) | ~v1_funct_2('#skF_6', A_696, B_695))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4961])).
% 22.01/13.18  tff(c_6374, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_6258, c_6361])).
% 22.01/13.18  tff(c_7147, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_6374])).
% 22.01/13.18  tff(c_7153, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_7147, c_4644])).
% 22.01/13.18  tff(c_6255, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_6250, c_470])).
% 22.01/13.18  tff(c_7379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4336, c_4332, c_7153, c_6255])).
% 22.01/13.18  tff(c_7380, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_6374])).
% 22.01/13.18  tff(c_7672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4336, c_4335, c_7380, c_6255])).
% 22.01/13.18  tff(c_7675, plain, (![A_777]: (~r2_hidden(A_777, '#skF_6'))), inference(splitRight, [status(thm)], [c_268])).
% 22.01/13.18  tff(c_7680, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_34, c_7675])).
% 22.01/13.18  tff(c_7698, plain, (![A_5]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_16])).
% 22.01/13.18  tff(c_8402, plain, (![B_874, C_875, A_876]: (B_874='#skF_6' | v1_partfun1(C_875, A_876) | ~v1_funct_2(C_875, A_876, B_874) | ~m1_subset_1(C_875, k1_zfmisc_1(k2_zfmisc_1(A_876, B_874))) | ~v1_funct_1(C_875))), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_68])).
% 22.01/13.18  tff(c_8409, plain, (![B_874, A_876]: (B_874='#skF_6' | v1_partfun1('#skF_6', A_876) | ~v1_funct_2('#skF_6', A_876, B_874) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_7698, c_8402])).
% 22.01/13.18  tff(c_8545, plain, (![B_891, A_892]: (B_891='#skF_6' | v1_partfun1('#skF_6', A_892) | ~v1_funct_2('#skF_6', A_892, B_891))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_8409])).
% 22.01/13.18  tff(c_8566, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_117, c_8545])).
% 22.01/13.18  tff(c_8568, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_8566])).
% 22.01/13.18  tff(c_7692, plain, (k6_partfun1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_278])).
% 22.01/13.18  tff(c_7732, plain, (![C_779, A_780, B_781]: (v4_relat_1(C_779, A_780) | ~m1_subset_1(C_779, k1_zfmisc_1(k2_zfmisc_1(A_780, B_781))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.01/13.18  tff(c_7748, plain, (![A_43]: (v4_relat_1(k6_partfun1(A_43), A_43))), inference(resolution, [status(thm)], [c_50, c_7732])).
% 22.01/13.18  tff(c_8079, plain, (![B_824, A_825]: (k1_relat_1(B_824)=A_825 | ~v1_partfun1(B_824, A_825) | ~v4_relat_1(B_824, A_825) | ~v1_relat_1(B_824))), inference(cnfTransformation, [status(thm)], [f_109])).
% 22.01/13.18  tff(c_8082, plain, (![A_43]: (k1_relat_1(k6_partfun1(A_43))=A_43 | ~v1_partfun1(k6_partfun1(A_43), A_43) | ~v1_relat_1(k6_partfun1(A_43)))), inference(resolution, [status(thm)], [c_7748, c_8079])).
% 22.01/13.18  tff(c_8098, plain, (![A_826]: (k1_relat_1(k6_partfun1(A_826))=A_826)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_48, c_8082])).
% 22.01/13.18  tff(c_8110, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_7692, c_8098])).
% 22.01/13.18  tff(c_7684, plain, (![A_146]: (v4_relat_1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_412])).
% 22.01/13.18  tff(c_8085, plain, (![A_146]: (k1_relat_1('#skF_6')=A_146 | ~v1_partfun1('#skF_6', A_146) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_7684, c_8079])).
% 22.01/13.18  tff(c_8094, plain, (![A_146]: (k1_relat_1('#skF_6')=A_146 | ~v1_partfun1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_8085])).
% 22.01/13.18  tff(c_8126, plain, (![A_146]: (A_146='#skF_6' | ~v1_partfun1('#skF_6', A_146))), inference(demodulation, [status(thm), theory('equality')], [c_8110, c_8094])).
% 22.01/13.18  tff(c_8573, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_8568, c_8126])).
% 22.01/13.18  tff(c_8578, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8573, c_433])).
% 22.01/13.18  tff(c_206, plain, (![B_4]: (m1_subset_1('#skF_2'(k1_xboole_0, B_4), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_203])).
% 22.01/13.18  tff(c_243, plain, (![A_128, B_4]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_128, '#skF_2'(k1_xboole_0, B_4)))), inference(resolution, [status(thm)], [c_206, c_239])).
% 22.01/13.18  tff(c_338, plain, (![A_137, B_138]: (~r2_hidden(A_137, '#skF_2'(k1_xboole_0, B_138)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_243])).
% 22.01/13.18  tff(c_343, plain, (![B_138]: ('#skF_2'(k1_xboole_0, B_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_338])).
% 22.01/13.18  tff(c_7863, plain, (![B_790]: ('#skF_2'('#skF_6', B_790)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_343])).
% 22.01/13.18  tff(c_7871, plain, (![B_790]: (v1_funct_2('#skF_6', '#skF_6', B_790))), inference(superposition, [status(thm), theory('equality')], [c_7863, c_52])).
% 22.01/13.18  tff(c_7688, plain, (![B_138]: ('#skF_2'('#skF_6', B_138)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_343])).
% 22.01/13.18  tff(c_8567, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_92, c_8545])).
% 22.01/13.18  tff(c_8569, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_8567])).
% 22.01/13.18  tff(c_10168, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_8573, c_8569])).
% 22.01/13.18  tff(c_10172, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_10168, c_8126])).
% 22.01/13.18  tff(c_7696, plain, (![B_4]: (k2_zfmisc_1('#skF_6', B_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_14])).
% 22.41/13.18  tff(c_8631, plain, (![D_893, A_894, B_895]: (v5_pre_topc(D_893, A_894, B_895) | ~v5_pre_topc(D_893, g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894)), B_895) | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)))) | ~v1_funct_2(D_893, u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)) | ~m1_subset_1(D_893, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_894), u1_struct_0(B_895)))) | ~v1_funct_2(D_893, u1_struct_0(A_894), u1_struct_0(B_895)) | ~v1_funct_1(D_893) | ~l1_pre_topc(B_895) | ~v2_pre_topc(B_895) | ~l1_pre_topc(A_894) | ~v2_pre_topc(A_894))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_8649, plain, (![A_894, B_895]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)), A_894, B_895) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)), g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894)), B_895) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)), u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_894), u1_struct_0(B_895)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895)), u1_struct_0(A_894), u1_struct_0(B_895)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_894), u1_pre_topc(A_894))), u1_struct_0(B_895))) | ~l1_pre_topc(B_895) | ~v2_pre_topc(B_895) | ~l1_pre_topc(A_894) | ~v2_pre_topc(A_894))), inference(resolution, [status(thm)], [c_62, c_8631])).
% 22.41/13.18  tff(c_10797, plain, (![A_1057, B_1058]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057), u1_pre_topc(A_1057))), u1_struct_0(B_1058)), A_1057, B_1058) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057), u1_pre_topc(A_1057))), u1_struct_0(B_1058)), g1_pre_topc(u1_struct_0(A_1057), u1_pre_topc(A_1057)), B_1058) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057), u1_pre_topc(A_1057))), u1_struct_0(B_1058)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1057), u1_struct_0(B_1058)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1057), u1_pre_topc(A_1057))), u1_struct_0(B_1058)), u1_struct_0(A_1057), u1_struct_0(B_1058)) | ~l1_pre_topc(B_1058) | ~v2_pre_topc(B_1058) | ~l1_pre_topc(A_1057) | ~v2_pre_topc(A_1057))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_8649])).
% 22.41/13.18  tff(c_10809, plain, (![B_1058]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_1058)), '#skF_3', B_1058) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_1058)), g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_1058) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_1058)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_1058)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_1058)), u1_struct_0('#skF_3'), u1_struct_0(B_1058)) | ~l1_pre_topc(B_1058) | ~v2_pre_topc(B_1058) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8573, c_10797])).
% 22.41/13.18  tff(c_11393, plain, (![B_1107]: (v5_pre_topc('#skF_6', '#skF_3', B_1107) | ~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_1107) | ~l1_pre_topc(B_1107) | ~v2_pre_topc(B_1107))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_7871, c_7688, c_10172, c_8573, c_8573, c_7698, c_7688, c_10172, c_7696, c_8573, c_8573, c_7688, c_10172, c_8573, c_7688, c_10172, c_8573, c_10809])).
% 22.41/13.18  tff(c_11409, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_8578, c_11393])).
% 22.41/13.18  tff(c_11416, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_11409])).
% 22.41/13.18  tff(c_11419, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_11416])).
% 22.41/13.18  tff(c_11423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_11419])).
% 22.41/13.18  tff(c_11424, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_11409])).
% 22.41/13.18  tff(c_11426, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_11424])).
% 22.41/13.18  tff(c_11429, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_456, c_11426])).
% 22.41/13.18  tff(c_11433, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_11429])).
% 22.41/13.18  tff(c_11434, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_11424])).
% 22.41/13.18  tff(c_8491, plain, (![D_886, A_887, B_888]: (v5_pre_topc(D_886, A_887, B_888) | ~v5_pre_topc(D_886, A_887, g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888))) | ~m1_subset_1(D_886, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))))) | ~v1_funct_2(D_886, u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))) | ~m1_subset_1(D_886, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887), u1_struct_0(B_888)))) | ~v1_funct_2(D_886, u1_struct_0(A_887), u1_struct_0(B_888)) | ~v1_funct_1(D_886) | ~l1_pre_topc(B_888) | ~v2_pre_topc(B_888) | ~l1_pre_topc(A_887) | ~v2_pre_topc(A_887))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.18  tff(c_8503, plain, (![A_887, B_888]: (v5_pre_topc('#skF_2'(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))), A_887, B_888) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))), A_887, g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))), u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_887), u1_struct_0(B_888)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888)))), u1_struct_0(A_887), u1_struct_0(B_888)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_887), u1_struct_0(g1_pre_topc(u1_struct_0(B_888), u1_pre_topc(B_888))))) | ~l1_pre_topc(B_888) | ~v2_pre_topc(B_888) | ~l1_pre_topc(A_887) | ~v2_pre_topc(A_887))), inference(resolution, [status(thm)], [c_62, c_8491])).
% 22.41/13.18  tff(c_10694, plain, (![A_1044, B_1045]: (v5_pre_topc('#skF_2'(u1_struct_0(A_1044), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), A_1044, B_1045) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_1044), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), A_1044, g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_1044), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1044), u1_struct_0(B_1045)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_1044), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), u1_struct_0(A_1044), u1_struct_0(B_1045)) | ~l1_pre_topc(B_1045) | ~v2_pre_topc(B_1045) | ~l1_pre_topc(A_1044) | ~v2_pre_topc(A_1044))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_8503])).
% 22.41/13.18  tff(c_10702, plain, (![B_1045]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), '#skF_3', B_1045) | ~v5_pre_topc('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), '#skF_3', g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045))) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_1045)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1045), u1_pre_topc(B_1045)))), u1_struct_0('#skF_3'), u1_struct_0(B_1045)) | ~l1_pre_topc(B_1045) | ~v2_pre_topc(B_1045) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8573, c_10694])).
% 22.41/13.18  tff(c_11649, plain, (![B_1130]: (v5_pre_topc('#skF_6', '#skF_3', B_1130) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_1130), u1_pre_topc(B_1130))) | ~l1_pre_topc(B_1130) | ~v2_pre_topc(B_1130))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_7871, c_7688, c_8573, c_8573, c_7698, c_7688, c_8573, c_8573, c_7688, c_7688, c_8573, c_10702])).
% 22.41/13.18  tff(c_11655, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_11434, c_11649])).
% 22.41/13.18  tff(c_11668, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_11655])).
% 22.41/13.18  tff(c_11670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_11668])).
% 22.41/13.18  tff(c_11671, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_8567])).
% 22.41/13.18  tff(c_11826, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11671, c_456])).
% 22.41/13.18  tff(c_16948, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_11826])).
% 22.41/13.18  tff(c_16951, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_456, c_16948])).
% 22.41/13.18  tff(c_16955, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_16951])).
% 22.41/13.18  tff(c_16957, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_11826])).
% 22.41/13.18  tff(c_11823, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11671, c_76])).
% 22.41/13.18  tff(c_17566, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16957, c_11823])).
% 22.41/13.18  tff(c_17567, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_17566])).
% 22.41/13.18  tff(c_17570, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_17567])).
% 22.41/13.18  tff(c_17574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_17570])).
% 22.41/13.18  tff(c_17576, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_17566])).
% 22.41/13.18  tff(c_11676, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_8568, c_8126])).
% 22.41/13.18  tff(c_17125, plain, (![A_1475, B_1476]: (v5_pre_topc('#skF_2'(u1_struct_0(A_1475), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), A_1475, B_1476) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_1475), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), A_1475, g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_1475), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1475), u1_struct_0(B_1476)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_1475), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), u1_struct_0(A_1475), u1_struct_0(B_1476)) | ~l1_pre_topc(B_1476) | ~v2_pre_topc(B_1476) | ~l1_pre_topc(A_1475) | ~v2_pre_topc(A_1475))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_8503])).
% 22.41/13.18  tff(c_17135, plain, (![B_1476]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), '#skF_3', B_1476) | ~v5_pre_topc('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), '#skF_3', g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476))) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_1476)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476)))), u1_struct_0('#skF_3'), u1_struct_0(B_1476)) | ~l1_pre_topc(B_1476) | ~v2_pre_topc(B_1476) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11676, c_17125])).
% 22.41/13.18  tff(c_17633, plain, (![B_1530]: (v5_pre_topc('#skF_6', '#skF_3', B_1530) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_1530), u1_pre_topc(B_1530))) | ~l1_pre_topc(B_1530) | ~v2_pre_topc(B_1530))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_7871, c_7688, c_11676, c_11676, c_7698, c_7688, c_11676, c_11676, c_7688, c_7688, c_11676, c_17135])).
% 22.41/13.18  tff(c_17639, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11671, c_17633])).
% 22.41/13.18  tff(c_17645, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_17576, c_16957, c_17639])).
% 22.41/13.18  tff(c_17649, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitLeft, [status(thm)], [c_17645])).
% 22.41/13.18  tff(c_16443, plain, (![D_1405, A_1406, B_1407]: (v5_pre_topc(D_1405, A_1406, g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407))) | ~v5_pre_topc(D_1405, A_1406, B_1407) | ~m1_subset_1(D_1405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))))) | ~v1_funct_2(D_1405, u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))) | ~m1_subset_1(D_1405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1406), u1_struct_0(B_1407)))) | ~v1_funct_2(D_1405, u1_struct_0(A_1406), u1_struct_0(B_1407)) | ~v1_funct_1(D_1405) | ~l1_pre_topc(B_1407) | ~v2_pre_topc(B_1407) | ~l1_pre_topc(A_1406) | ~v2_pre_topc(A_1406))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.18  tff(c_16470, plain, (![A_1406, B_1407]: (v5_pre_topc('#skF_2'(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))), A_1406, g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))), A_1406, B_1407) | ~v1_funct_2('#skF_2'(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))), u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1406), u1_struct_0(B_1407)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407)))), u1_struct_0(A_1406), u1_struct_0(B_1407)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_1406), u1_struct_0(g1_pre_topc(u1_struct_0(B_1407), u1_pre_topc(B_1407))))) | ~l1_pre_topc(B_1407) | ~v2_pre_topc(B_1407) | ~l1_pre_topc(A_1406) | ~v2_pre_topc(A_1406))), inference(resolution, [status(thm)], [c_62, c_16443])).
% 22.41/13.18  tff(c_16988, plain, (![A_1466, B_1467]: (v5_pre_topc('#skF_2'(u1_struct_0(A_1466), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), A_1466, g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_1466), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), A_1466, B_1467) | ~m1_subset_1('#skF_2'(u1_struct_0(A_1466), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1466), u1_struct_0(B_1467)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_1466), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), u1_struct_0(A_1466), u1_struct_0(B_1467)) | ~l1_pre_topc(B_1467) | ~v2_pre_topc(B_1467) | ~l1_pre_topc(A_1466) | ~v2_pre_topc(A_1466))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_16470])).
% 22.41/13.18  tff(c_17004, plain, (![B_1467]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), '#skF_3', g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467))) | ~v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), '#skF_3', B_1467) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0(B_1467)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1467), u1_pre_topc(B_1467)))), u1_struct_0('#skF_3'), u1_struct_0(B_1467)) | ~l1_pre_topc(B_1467) | ~v2_pre_topc(B_1467) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_11676, c_16988])).
% 22.41/13.18  tff(c_17553, plain, (![B_1528]: (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_1528), u1_pre_topc(B_1528))) | ~v5_pre_topc('#skF_6', '#skF_3', B_1528) | ~l1_pre_topc(B_1528) | ~v2_pre_topc(B_1528))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_7871, c_7688, c_11676, c_11676, c_7698, c_7688, c_11676, c_7688, c_11676, c_7688, c_11676, c_17004])).
% 22.41/13.18  tff(c_17556, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_11671, c_17553])).
% 22.41/13.18  tff(c_17561, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_16957, c_17556])).
% 22.41/13.18  tff(c_19578, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_17576, c_17561])).
% 22.41/13.18  tff(c_19579, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_17649, c_19578])).
% 22.41/13.18  tff(c_11681, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11676, c_433])).
% 22.41/13.18  tff(c_409, plain, (![A_146]: (v1_funct_2(k1_xboole_0, A_146, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_398, c_52])).
% 22.41/13.18  tff(c_7683, plain, (![A_146]: (v1_funct_2('#skF_6', A_146, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_409])).
% 22.41/13.18  tff(c_394, plain, (![A_145]: ('#skF_2'(A_145, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_386])).
% 22.41/13.18  tff(c_7685, plain, (![A_145]: ('#skF_2'(A_145, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_394])).
% 22.41/13.18  tff(c_11734, plain, (![D_1131, A_1132, B_1133]: (v5_pre_topc(D_1131, A_1132, B_1133) | ~v5_pre_topc(D_1131, g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132)), B_1133) | ~m1_subset_1(D_1131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)))) | ~v1_funct_2(D_1131, u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)) | ~m1_subset_1(D_1131, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1132), u1_struct_0(B_1133)))) | ~v1_funct_2(D_1131, u1_struct_0(A_1132), u1_struct_0(B_1133)) | ~v1_funct_1(D_1131) | ~l1_pre_topc(B_1133) | ~v2_pre_topc(B_1133) | ~l1_pre_topc(A_1132) | ~v2_pre_topc(A_1132))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_11752, plain, (![A_1132, B_1133]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)), A_1132, B_1133) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)), g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132)), B_1133) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)), u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1132), u1_struct_0(B_1133)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133)), u1_struct_0(A_1132), u1_struct_0(B_1133)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1132), u1_pre_topc(A_1132))), u1_struct_0(B_1133))) | ~l1_pre_topc(B_1133) | ~v2_pre_topc(B_1133) | ~l1_pre_topc(A_1132) | ~v2_pre_topc(A_1132))), inference(resolution, [status(thm)], [c_62, c_11734])).
% 22.41/13.18  tff(c_17263, plain, (![A_1496, B_1497]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(B_1497)), A_1496, B_1497) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(B_1497)), g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496)), B_1497) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(B_1497)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1496), u1_struct_0(B_1497)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(B_1497)), u1_struct_0(A_1496), u1_struct_0(B_1497)) | ~l1_pre_topc(B_1497) | ~v2_pre_topc(B_1497) | ~l1_pre_topc(A_1496) | ~v2_pre_topc(A_1496))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_11752])).
% 22.41/13.18  tff(c_17269, plain, (![A_1496]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_1496, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), '#skF_6'), g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1496), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_1496), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_1496) | ~v2_pre_topc(A_1496))), inference(superposition, [status(thm), theory('equality')], [c_11671, c_17263])).
% 22.41/13.18  tff(c_17283, plain, (![A_1496]: (v5_pre_topc('#skF_6', A_1496, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_1496), u1_pre_topc(A_1496)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_1496) | ~v2_pre_topc(A_1496))), inference(demodulation, [status(thm), theory('equality')], [c_16957, c_7683, c_7685, c_11671, c_11671, c_7698, c_7685, c_11671, c_11671, c_7685, c_7685, c_11671, c_17269])).
% 22.41/13.18  tff(c_19838, plain, (![A_1648]: (v5_pre_topc('#skF_6', A_1648, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_1648), u1_pre_topc(A_1648)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_1648) | ~v2_pre_topc(A_1648))), inference(demodulation, [status(thm), theory('equality')], [c_17576, c_17283])).
% 22.41/13.18  tff(c_19858, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11676, c_19838])).
% 22.41/13.18  tff(c_19873, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_11681, c_19858])).
% 22.41/13.18  tff(c_19875, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19579, c_19873])).
% 22.41/13.18  tff(c_19876, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_17645])).
% 22.41/13.18  tff(c_17149, plain, (![B_1476]: (v5_pre_topc('#skF_6', '#skF_3', B_1476) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_1476), u1_pre_topc(B_1476))) | ~l1_pre_topc(B_1476) | ~v2_pre_topc(B_1476))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_7871, c_7688, c_11676, c_11676, c_7698, c_7688, c_11676, c_11676, c_7688, c_7688, c_11676, c_17135])).
% 22.41/13.18  tff(c_19880, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_19876, c_17149])).
% 22.41/13.18  tff(c_19883, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_19880])).
% 22.41/13.18  tff(c_19885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_19883])).
% 22.41/13.18  tff(c_19886, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_8566])).
% 22.41/13.18  tff(c_19891, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_19886, c_433])).
% 22.41/13.18  tff(c_28114, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_19886, c_8567])).
% 22.41/13.18  tff(c_28115, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_28114])).
% 22.41/13.18  tff(c_28179, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_28115, c_8126])).
% 22.41/13.18  tff(c_7852, plain, (![A_787, B_788]: (v1_pre_topc(g1_pre_topc(A_787, B_788)) | ~m1_subset_1(B_788, k1_zfmisc_1(k1_zfmisc_1(A_787))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 22.41/13.18  tff(c_7861, plain, (![A_53]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(A_53))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_74, c_7852])).
% 22.41/13.18  tff(c_28222, plain, (v1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28179, c_7861])).
% 22.41/13.18  tff(c_28994, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_28222])).
% 22.41/13.18  tff(c_28997, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_456, c_28994])).
% 22.41/13.18  tff(c_29001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_28997])).
% 22.41/13.18  tff(c_29003, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_28222])).
% 22.41/13.18  tff(c_7695, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | A_24='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_34])).
% 22.41/13.18  tff(c_28231, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28179, c_74])).
% 22.41/13.18  tff(c_29306, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_29003, c_28231])).
% 22.41/13.18  tff(c_18, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 22.41/13.18  tff(c_29323, plain, (![A_2220]: (m1_subset_1(A_2220, k1_zfmisc_1('#skF_6')) | ~r2_hidden(A_2220, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(resolution, [status(thm)], [c_29306, c_18])).
% 22.41/13.18  tff(c_29328, plain, (m1_subset_1('#skF_1'(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), k1_zfmisc_1('#skF_6')) | u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_7695, c_29323])).
% 22.41/13.18  tff(c_29599, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(splitLeft, [status(thm)], [c_29328])).
% 22.41/13.18  tff(c_29754, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_6')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_29599, c_76])).
% 22.41/13.18  tff(c_29824, plain, (v2_pre_topc(g1_pre_topc('#skF_6', '#skF_6')) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_29003, c_28179, c_29754])).
% 22.41/13.18  tff(c_29830, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_29824])).
% 22.41/13.18  tff(c_29833, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_29830])).
% 22.41/13.18  tff(c_29837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_29833])).
% 22.41/13.18  tff(c_29839, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_29824])).
% 22.41/13.18  tff(c_28141, plain, (![D_2102, A_2103, B_2104]: (v5_pre_topc(D_2102, g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103)), B_2104) | ~v5_pre_topc(D_2102, A_2103, B_2104) | ~m1_subset_1(D_2102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)))) | ~v1_funct_2(D_2102, u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)) | ~m1_subset_1(D_2102, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2103), u1_struct_0(B_2104)))) | ~v1_funct_2(D_2102, u1_struct_0(A_2103), u1_struct_0(B_2104)) | ~v1_funct_1(D_2102) | ~l1_pre_topc(B_2104) | ~v2_pre_topc(B_2104) | ~l1_pre_topc(A_2103) | ~v2_pre_topc(A_2103))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_28159, plain, (![A_2103, B_2104]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)), g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103)), B_2104) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)), A_2103, B_2104) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)), u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2103), u1_struct_0(B_2104)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104)), u1_struct_0(A_2103), u1_struct_0(B_2104)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2103), u1_pre_topc(A_2103))), u1_struct_0(B_2104))) | ~l1_pre_topc(B_2104) | ~v2_pre_topc(B_2104) | ~l1_pre_topc(A_2103) | ~v2_pre_topc(A_2103))), inference(resolution, [status(thm)], [c_62, c_28141])).
% 22.41/13.18  tff(c_29004, plain, (![A_2195, B_2196]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0(B_2196)), g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195)), B_2196) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0(B_2196)), A_2195, B_2196) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0(B_2196)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195), u1_struct_0(B_2196)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0(B_2196)), u1_struct_0(A_2195), u1_struct_0(B_2196)) | ~l1_pre_topc(B_2196) | ~v2_pre_topc(B_2196) | ~l1_pre_topc(A_2195) | ~v2_pre_topc(A_2195))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_28159])).
% 22.41/13.18  tff(c_29024, plain, (![A_2195]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0('#skF_4')), g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195)), '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0('#skF_4')), A_2195, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2195), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195))), u1_struct_0('#skF_4')), u1_struct_0(A_2195), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_2195) | ~v2_pre_topc(A_2195))), inference(superposition, [status(thm), theory('equality')], [c_19886, c_29004])).
% 22.41/13.18  tff(c_29044, plain, (![A_2195]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2195), u1_pre_topc(A_2195)), '#skF_4') | ~v5_pre_topc('#skF_6', A_2195, '#skF_4') | ~l1_pre_topc(A_2195) | ~v2_pre_topc(A_2195))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_7683, c_7685, c_19886, c_19886, c_7698, c_7685, c_19886, c_7685, c_19886, c_7685, c_19886, c_29024])).
% 22.41/13.18  tff(c_29706, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_6'), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_29599, c_29044])).
% 22.41/13.18  tff(c_29788, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', '#skF_6'), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_29003, c_28179, c_29706])).
% 22.41/13.18  tff(c_30095, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', '#skF_6'), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29839, c_29788])).
% 22.41/13.18  tff(c_30096, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_30095])).
% 22.41/13.18  tff(c_7699, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_7680, c_7680, c_12])).
% 22.41/13.18  tff(c_84, plain, (![D_84, A_70, B_78]: (v5_pre_topc(D_84, A_70, B_78) | ~v5_pre_topc(D_84, A_70, g1_pre_topc(u1_struct_0(B_78), u1_pre_topc(B_78))) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70), u1_struct_0(g1_pre_topc(u1_struct_0(B_78), u1_pre_topc(B_78)))))) | ~v1_funct_2(D_84, u1_struct_0(A_70), u1_struct_0(g1_pre_topc(u1_struct_0(B_78), u1_pre_topc(B_78)))) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70), u1_struct_0(B_78)))) | ~v1_funct_2(D_84, u1_struct_0(A_70), u1_struct_0(B_78)) | ~v1_funct_1(D_84) | ~l1_pre_topc(B_78) | ~v2_pre_topc(B_78) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.18  tff(c_19901, plain, (![D_84, A_70]: (v5_pre_topc(D_84, A_70, '#skF_4') | ~v5_pre_topc(D_84, A_70, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))) | ~v1_funct_2(D_84, u1_struct_0(A_70), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_70), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_84, u1_struct_0(A_70), u1_struct_0('#skF_4')) | ~v1_funct_1(D_84) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70))), inference(superposition, [status(thm), theory('equality')], [c_19886, c_84])).
% 22.41/13.18  tff(c_32254, plain, (![D_2339, A_2340]: (v5_pre_topc(D_2339, A_2340, '#skF_4') | ~v5_pre_topc(D_2339, A_2340, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~m1_subset_1(D_2339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2340), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))) | ~v1_funct_2(D_2339, u1_struct_0(A_2340), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~m1_subset_1(D_2339, k1_zfmisc_1('#skF_6')) | ~v1_funct_2(D_2339, u1_struct_0(A_2340), '#skF_6') | ~v1_funct_1(D_2339) | ~l1_pre_topc(A_2340) | ~v2_pre_topc(A_2340))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_19886, c_7699, c_19886, c_19886, c_19886, c_19901])).
% 22.41/13.18  tff(c_32276, plain, (![A_2340]: (v5_pre_topc('#skF_6', A_2340, '#skF_4') | ~v5_pre_topc('#skF_6', A_2340, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2340), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0(A_2340), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc(A_2340) | ~v2_pre_topc(A_2340))), inference(resolution, [status(thm)], [c_7698, c_32254])).
% 22.41/13.18  tff(c_32308, plain, (![A_2341]: (v5_pre_topc('#skF_6', A_2341, '#skF_4') | ~v5_pre_topc('#skF_6', A_2341, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2341), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~l1_pre_topc(A_2341) | ~v2_pre_topc(A_2341))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_7683, c_7698, c_32276])).
% 22.41/13.18  tff(c_32311, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', '#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_28179, c_32308])).
% 22.41/13.18  tff(c_32319, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_29839, c_29003, c_7871, c_19891, c_32311])).
% 22.41/13.18  tff(c_32321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30096, c_32319])).
% 22.41/13.18  tff(c_32323, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_30095])).
% 22.41/13.18  tff(c_28285, plain, (![D_2110, A_2111, B_2112]: (v5_pre_topc(D_2110, A_2111, B_2112) | ~v5_pre_topc(D_2110, g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111)), B_2112) | ~m1_subset_1(D_2110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)))) | ~v1_funct_2(D_2110, u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)) | ~m1_subset_1(D_2110, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2111), u1_struct_0(B_2112)))) | ~v1_funct_2(D_2110, u1_struct_0(A_2111), u1_struct_0(B_2112)) | ~v1_funct_1(D_2110) | ~l1_pre_topc(B_2112) | ~v2_pre_topc(B_2112) | ~l1_pre_topc(A_2111) | ~v2_pre_topc(A_2111))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_28312, plain, (![A_2111, B_2112]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)), A_2111, B_2112) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)), g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111)), B_2112) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)), u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2111), u1_struct_0(B_2112)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112)), u1_struct_0(A_2111), u1_struct_0(B_2112)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2111), u1_pre_topc(A_2111))), u1_struct_0(B_2112))) | ~l1_pre_topc(B_2112) | ~v2_pre_topc(B_2112) | ~l1_pre_topc(A_2111) | ~v2_pre_topc(A_2111))), inference(resolution, [status(thm)], [c_62, c_28285])).
% 22.41/13.18  tff(c_28673, plain, (![A_2150, B_2151]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0(B_2151)), A_2150, B_2151) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0(B_2151)), g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150)), B_2151) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0(B_2151)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2150), u1_struct_0(B_2151)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0(B_2151)), u1_struct_0(A_2150), u1_struct_0(B_2151)) | ~l1_pre_topc(B_2151) | ~v2_pre_topc(B_2151) | ~l1_pre_topc(A_2150) | ~v2_pre_topc(A_2150))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_28312])).
% 22.41/13.18  tff(c_28685, plain, (![A_2150]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0('#skF_4')), A_2150, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), '#skF_6'), g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150)), '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2150), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150))), u1_struct_0('#skF_4')), u1_struct_0(A_2150), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_2150) | ~v2_pre_topc(A_2150))), inference(superposition, [status(thm), theory('equality')], [c_19886, c_28673])).
% 22.41/13.18  tff(c_28697, plain, (![A_2150]: (v5_pre_topc('#skF_6', A_2150, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2150), u1_pre_topc(A_2150)), '#skF_4') | ~l1_pre_topc(A_2150) | ~v2_pre_topc(A_2150))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_7683, c_7685, c_19886, c_19886, c_7698, c_7685, c_19886, c_19886, c_7685, c_7685, c_19886, c_28685])).
% 22.41/13.18  tff(c_32388, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32323, c_28697])).
% 22.41/13.18  tff(c_32391, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_32388])).
% 22.41/13.18  tff(c_32393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_32391])).
% 22.41/13.18  tff(c_32394, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_28114])).
% 22.41/13.18  tff(c_33278, plain, (![A_2418, B_2419]: (v5_pre_topc('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0(B_2419), u1_pre_topc(B_2419)))), A_2418, B_2419) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0(B_2419), u1_pre_topc(B_2419)))), A_2418, g1_pre_topc(u1_struct_0(B_2419), u1_pre_topc(B_2419))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0(B_2419), u1_pre_topc(B_2419)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2418), u1_struct_0(B_2419)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0(B_2419), u1_pre_topc(B_2419)))), u1_struct_0(A_2418), u1_struct_0(B_2419)) | ~l1_pre_topc(B_2419) | ~v2_pre_topc(B_2419) | ~l1_pre_topc(A_2418) | ~v2_pre_topc(A_2418))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_8503])).
% 22.41/13.18  tff(c_33294, plain, (![A_2418]: (v5_pre_topc('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_2418, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_2418, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2418), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_2418), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_2418), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_2418) | ~v2_pre_topc(A_2418))), inference(superposition, [status(thm), theory('equality')], [c_19886, c_33278])).
% 22.41/13.18  tff(c_33615, plain, (![A_2458]: (v5_pre_topc('#skF_6', A_2458, '#skF_4') | ~v5_pre_topc('#skF_6', A_2458, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_2458) | ~v2_pre_topc(A_2458))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_7683, c_7685, c_32394, c_19886, c_19886, c_7698, c_7685, c_32394, c_7699, c_19886, c_19886, c_7685, c_32394, c_19886, c_7685, c_32394, c_19886, c_33294])).
% 22.41/13.18  tff(c_33630, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_19891, c_33615])).
% 22.41/13.18  tff(c_33713, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_33630])).
% 22.41/13.18  tff(c_33716, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_33713])).
% 22.41/13.18  tff(c_33720, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_33716])).
% 22.41/13.18  tff(c_33721, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_33630])).
% 22.41/13.18  tff(c_33723, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_33721])).
% 22.41/13.18  tff(c_33726, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_456, c_33723])).
% 22.41/13.18  tff(c_33730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_33726])).
% 22.41/13.18  tff(c_33731, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_33721])).
% 22.41/13.18  tff(c_32592, plain, (![D_2354, A_2355, B_2356]: (v5_pre_topc(D_2354, A_2355, B_2356) | ~v5_pre_topc(D_2354, g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355)), B_2356) | ~m1_subset_1(D_2354, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)))) | ~v1_funct_2(D_2354, u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)) | ~m1_subset_1(D_2354, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2355), u1_struct_0(B_2356)))) | ~v1_funct_2(D_2354, u1_struct_0(A_2355), u1_struct_0(B_2356)) | ~v1_funct_1(D_2354) | ~l1_pre_topc(B_2356) | ~v2_pre_topc(B_2356) | ~l1_pre_topc(A_2355) | ~v2_pre_topc(A_2355))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_32616, plain, (![A_2355, B_2356]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)), A_2355, B_2356) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)), g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355)), B_2356) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)), u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2355), u1_struct_0(B_2356)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356)), u1_struct_0(A_2355), u1_struct_0(B_2356)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2355), u1_pre_topc(A_2355))), u1_struct_0(B_2356))) | ~l1_pre_topc(B_2356) | ~v2_pre_topc(B_2356) | ~l1_pre_topc(A_2355) | ~v2_pre_topc(A_2355))), inference(resolution, [status(thm)], [c_62, c_32592])).
% 22.41/13.18  tff(c_32999, plain, (![A_2393, B_2394]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0(B_2394)), A_2393, B_2394) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0(B_2394)), g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393)), B_2394) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0(B_2394)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2393), u1_struct_0(B_2394)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0(B_2394)), u1_struct_0(A_2393), u1_struct_0(B_2394)) | ~l1_pre_topc(B_2394) | ~v2_pre_topc(B_2394) | ~l1_pre_topc(A_2393) | ~v2_pre_topc(A_2393))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_32616])).
% 22.41/13.18  tff(c_33009, plain, (![A_2393]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0('#skF_4')), A_2393, '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), '#skF_6'), g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393)), '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0('#skF_4')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2393), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2393), u1_pre_topc(A_2393))), u1_struct_0('#skF_4')), u1_struct_0(A_2393), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_2393) | ~v2_pre_topc(A_2393))), inference(superposition, [status(thm), theory('equality')], [c_19886, c_32999])).
% 22.41/13.18  tff(c_33971, plain, (![A_2476]: (v5_pre_topc('#skF_6', A_2476, '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2476), u1_pre_topc(A_2476)), '#skF_4') | ~l1_pre_topc(A_2476) | ~v2_pre_topc(A_2476))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_7683, c_7685, c_19886, c_19886, c_7698, c_7685, c_19886, c_19886, c_7685, c_7685, c_19886, c_33009])).
% 22.41/13.18  tff(c_33977, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_33731, c_33971])).
% 22.41/13.18  tff(c_33990, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_33977])).
% 22.41/13.18  tff(c_33992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_33990])).
% 22.41/13.18  tff(c_33994, plain, (v5_pre_topc('#skF_6', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_120])).
% 22.41/13.18  tff(c_34204, plain, (![C_2506, A_2507, B_2508]: (v4_relat_1(C_2506, A_2507) | ~m1_subset_1(C_2506, k1_zfmisc_1(k2_zfmisc_1(A_2507, B_2508))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.41/13.18  tff(c_34229, plain, (v4_relat_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_121, c_34204])).
% 22.41/13.18  tff(c_34354, plain, (![B_2541, A_2542]: (k1_relat_1(B_2541)=A_2542 | ~v1_partfun1(B_2541, A_2542) | ~v4_relat_1(B_2541, A_2542) | ~v1_relat_1(B_2541))), inference(cnfTransformation, [status(thm)], [f_109])).
% 22.41/13.18  tff(c_34363, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34229, c_34354])).
% 22.41/13.18  tff(c_34378, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_34363])).
% 22.41/13.18  tff(c_34420, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_34378])).
% 22.41/13.18  tff(c_34757, plain, (![B_2596, C_2597, A_2598]: (k1_xboole_0=B_2596 | v1_partfun1(C_2597, A_2598) | ~v1_funct_2(C_2597, A_2598, B_2596) | ~m1_subset_1(C_2597, k1_zfmisc_1(k2_zfmisc_1(A_2598, B_2596))) | ~v1_funct_1(C_2597))), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.41/13.18  tff(c_34769, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_121, c_34757])).
% 22.41/13.18  tff(c_34795, plain, (u1_struct_0('#skF_4')=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_117, c_34769])).
% 22.41/13.18  tff(c_34796, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34420, c_34795])).
% 22.41/13.18  tff(c_34253, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_263])).
% 22.41/13.18  tff(c_34812, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_34796, c_34253])).
% 22.41/13.18  tff(c_34822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_34812])).
% 22.41/13.18  tff(c_34823, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_34378])).
% 22.41/13.18  tff(c_33993, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_120])).
% 22.41/13.18  tff(c_34827, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34823, c_33993])).
% 22.41/13.18  tff(c_34833, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_34823, c_90])).
% 22.41/13.18  tff(c_35086, plain, (![D_2630, B_2631, C_2632, A_2633]: (m1_subset_1(D_2630, k1_zfmisc_1(k2_zfmisc_1(B_2631, C_2632))) | ~r1_tarski(k1_relat_1(D_2630), B_2631) | ~m1_subset_1(D_2630, k1_zfmisc_1(k2_zfmisc_1(A_2633, C_2632))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 22.41/13.18  tff(c_35102, plain, (![B_2631]: (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_2631, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~r1_tarski(k1_relat_1('#skF_6'), B_2631))), inference(resolution, [status(thm)], [c_34833, c_35086])).
% 22.41/13.18  tff(c_35551, plain, (![D_2677, A_2678, B_2679]: (v5_pre_topc(D_2677, A_2678, B_2679) | ~v5_pre_topc(D_2677, g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678)), B_2679) | ~m1_subset_1(D_2677, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678))), u1_struct_0(B_2679)))) | ~v1_funct_2(D_2677, u1_struct_0(g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678))), u1_struct_0(B_2679)) | ~m1_subset_1(D_2677, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2678), u1_struct_0(B_2679)))) | ~v1_funct_2(D_2677, u1_struct_0(A_2678), u1_struct_0(B_2679)) | ~v1_funct_1(D_2677) | ~l1_pre_topc(B_2679) | ~v2_pre_topc(B_2679) | ~l1_pre_topc(A_2678) | ~v2_pre_topc(A_2678))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_35559, plain, (![A_2678]: (v5_pre_topc('#skF_6', A_2678, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2678), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2678), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_2678) | ~v2_pre_topc(A_2678) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678)))))), inference(resolution, [status(thm)], [c_35102, c_35551])).
% 22.41/13.18  tff(c_35587, plain, (![A_2678]: (v5_pre_topc('#skF_6', A_2678, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2678), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2678), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_2678) | ~v2_pre_topc(A_2678) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2678), u1_pre_topc(A_2678)))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_35559])).
% 22.41/13.18  tff(c_37405, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_35587])).
% 22.41/13.18  tff(c_37408, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_37405])).
% 22.41/13.18  tff(c_37412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_37408])).
% 22.41/13.18  tff(c_37414, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_35587])).
% 22.41/13.18  tff(c_35946, plain, (![D_2709, A_2710, B_2711]: (v5_pre_topc(D_2709, g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)), B_2711) | ~v5_pre_topc(D_2709, A_2710, B_2711) | ~m1_subset_1(D_2709, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710))), u1_struct_0(B_2711)))) | ~v1_funct_2(D_2709, u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710))), u1_struct_0(B_2711)) | ~m1_subset_1(D_2709, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710), u1_struct_0(B_2711)))) | ~v1_funct_2(D_2709, u1_struct_0(A_2710), u1_struct_0(B_2711)) | ~v1_funct_1(D_2709) | ~l1_pre_topc(B_2711) | ~v2_pre_topc(B_2711) | ~l1_pre_topc(A_2710) | ~v2_pre_topc(A_2710))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_35964, plain, (![A_2710]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_2710, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2710), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_2710) | ~v2_pre_topc(A_2710) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)))))), inference(resolution, [status(thm)], [c_35102, c_35946])).
% 22.41/13.18  tff(c_35999, plain, (![A_2710]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_2710, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2710), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_2710) | ~v2_pre_topc(A_2710) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_35964])).
% 22.41/13.18  tff(c_37507, plain, (![A_2710]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_2710, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2710), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2710), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_2710) | ~v2_pre_topc(A_2710) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(A_2710), u1_pre_topc(A_2710)))))), inference(demodulation, [status(thm), theory('equality')], [c_37414, c_35999])).
% 22.41/13.18  tff(c_37508, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_37507])).
% 22.41/13.18  tff(c_37511, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34171, c_37508])).
% 22.41/13.18  tff(c_37515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_37511])).
% 22.41/13.18  tff(c_37517, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_37507])).
% 22.41/13.18  tff(c_34834, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_34823, c_92])).
% 22.41/13.18  tff(c_35277, plain, (![B_2648, C_2649, A_2650]: (k1_xboole_0=B_2648 | v1_partfun1(C_2649, A_2650) | ~v1_funct_2(C_2649, A_2650, B_2648) | ~m1_subset_1(C_2649, k1_zfmisc_1(k2_zfmisc_1(A_2650, B_2648))) | ~v1_funct_1(C_2649))), inference(cnfTransformation, [status(thm)], [f_145])).
% 22.41/13.18  tff(c_35286, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_34833, c_35277])).
% 22.41/13.18  tff(c_35312, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_xboole_0 | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_34834, c_35286])).
% 22.41/13.18  tff(c_35624, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_35312])).
% 22.41/13.18  tff(c_34231, plain, (v4_relat_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_90, c_34204])).
% 22.41/13.18  tff(c_34357, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_34231, c_34354])).
% 22.41/13.18  tff(c_34372, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_34357])).
% 22.41/13.18  tff(c_35841, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35624, c_34823, c_34823, c_34372])).
% 22.41/13.18  tff(c_35847, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_35841, c_34834])).
% 22.41/13.18  tff(c_34832, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34823, c_117])).
% 22.41/13.18  tff(c_34831, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_34823, c_121])).
% 22.41/13.18  tff(c_35424, plain, (![D_2664, A_2665, B_2666]: (v5_pre_topc(D_2664, A_2665, g1_pre_topc(u1_struct_0(B_2666), u1_pre_topc(B_2666))) | ~v5_pre_topc(D_2664, A_2665, B_2666) | ~m1_subset_1(D_2664, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2665), u1_struct_0(g1_pre_topc(u1_struct_0(B_2666), u1_pre_topc(B_2666)))))) | ~v1_funct_2(D_2664, u1_struct_0(A_2665), u1_struct_0(g1_pre_topc(u1_struct_0(B_2666), u1_pre_topc(B_2666)))) | ~m1_subset_1(D_2664, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2665), u1_struct_0(B_2666)))) | ~v1_funct_2(D_2664, u1_struct_0(A_2665), u1_struct_0(B_2666)) | ~v1_funct_1(D_2664) | ~l1_pre_topc(B_2666) | ~v2_pre_topc(B_2666) | ~l1_pre_topc(A_2665) | ~v2_pre_topc(A_2665))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.18  tff(c_35428, plain, (![A_2665]: (v5_pre_topc('#skF_6', A_2665, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_2665, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_2665), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2665), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2665), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_2665) | ~v2_pre_topc(A_2665) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(A_2665)))), inference(resolution, [status(thm)], [c_35102, c_35424])).
% 22.41/13.18  tff(c_37063, plain, (![A_2830]: (v5_pre_topc('#skF_6', A_2830, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_2830, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_2830), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2830), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(A_2830), u1_struct_0('#skF_4')) | ~l1_pre_topc(A_2830) | ~v2_pre_topc(A_2830) | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0(A_2830)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_94, c_35428])).
% 22.41/13.18  tff(c_37072, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski(k1_relat_1('#skF_6'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34823, c_37063])).
% 22.41/13.18  tff(c_37078, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_34823, c_108, c_106, c_34832, c_34823, c_34831, c_34823, c_35847, c_33994, c_37072])).
% 22.41/13.18  tff(c_35846, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))))), inference(demodulation, [status(thm), theory('equality')], [c_35841, c_34833])).
% 22.41/13.18  tff(c_35971, plain, (![D_2709, B_2711]: (v5_pre_topc(D_2709, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_2711) | ~v5_pre_topc(D_2709, '#skF_3', B_2711) | ~m1_subset_1(D_2709, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(B_2711)))) | ~v1_funct_2(D_2709, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_2711)) | ~m1_subset_1(D_2709, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_2711)))) | ~v1_funct_2(D_2709, u1_struct_0('#skF_3'), u1_struct_0(B_2711)) | ~v1_funct_1(D_2709) | ~l1_pre_topc(B_2711) | ~v2_pre_topc(B_2711) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_34823, c_35946])).
% 22.41/13.18  tff(c_38020, plain, (![D_2886, B_2887]: (v5_pre_topc(D_2886, g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), B_2887) | ~v5_pre_topc(D_2886, '#skF_3', B_2887) | ~m1_subset_1(D_2886, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_2887)))) | ~v1_funct_2(D_2886, k1_relat_1('#skF_6'), u1_struct_0(B_2887)) | ~v1_funct_1(D_2886) | ~l1_pre_topc(B_2887) | ~v2_pre_topc(B_2887))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_34823, c_34823, c_35841, c_34823, c_35841, c_34823, c_35971])).
% 22.41/13.18  tff(c_38027, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_35846, c_38020])).
% 22.41/13.18  tff(c_38064, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_37414, c_37517, c_94, c_35847, c_37078, c_38027])).
% 22.41/13.18  tff(c_38066, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34827, c_38064])).
% 22.41/13.18  tff(c_38067, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_35312])).
% 22.41/13.18  tff(c_34180, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitLeft, [status(thm)], [c_268])).
% 22.41/13.18  tff(c_34982, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_34823, c_34180])).
% 22.41/13.18  tff(c_38071, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_3'))), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_38067, c_34982])).
% 22.41/13.18  tff(c_38079, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_12, c_38071])).
% 22.41/13.18  tff(c_38082, plain, (![A_2888]: (~r2_hidden(A_2888, '#skF_6'))), inference(splitRight, [status(thm)], [c_263])).
% 22.41/13.18  tff(c_38087, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_34, c_38082])).
% 22.41/13.18  tff(c_38109, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_2])).
% 22.41/13.18  tff(c_38108, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_38087, c_12])).
% 22.41/13.18  tff(c_38105, plain, (![B_4]: (k2_zfmisc_1('#skF_6', B_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_38087, c_14])).
% 22.41/13.18  tff(c_38081, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_263])).
% 22.41/13.18  tff(c_38104, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | A_24='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_34])).
% 22.41/13.18  tff(c_38484, plain, (![A_2929, B_2930, A_2931]: (~v1_xboole_0(k2_zfmisc_1(A_2929, B_2930)) | ~r2_hidden(A_2931, '#skF_2'(A_2929, B_2930)))), inference(resolution, [status(thm)], [c_62, c_239])).
% 22.41/13.18  tff(c_38545, plain, (![A_2938, B_2939]: (~v1_xboole_0(k2_zfmisc_1(A_2938, B_2939)) | '#skF_2'(A_2938, B_2939)='#skF_6')), inference(resolution, [status(thm)], [c_38104, c_38484])).
% 22.41/13.18  tff(c_38555, plain, ('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))='#skF_6'), inference(resolution, [status(thm)], [c_38081, c_38545])).
% 22.41/13.18  tff(c_38630, plain, (![B_2955, C_2956, A_2957]: (B_2955='#skF_6' | v1_partfun1(C_2956, A_2957) | ~v1_funct_2(C_2956, A_2957, B_2955) | ~m1_subset_1(C_2956, k1_zfmisc_1(k2_zfmisc_1(A_2957, B_2955))) | ~v1_funct_1(C_2956))), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_68])).
% 22.41/13.18  tff(c_38643, plain, (![B_45, A_44]: (B_45='#skF_6' | v1_partfun1('#skF_2'(A_44, B_45), A_44) | ~v1_funct_2('#skF_2'(A_44, B_45), A_44, B_45) | ~v1_funct_1('#skF_2'(A_44, B_45)))), inference(resolution, [status(thm)], [c_62, c_38630])).
% 22.41/13.18  tff(c_38656, plain, (![B_2958, A_2959]: (B_2958='#skF_6' | v1_partfun1('#skF_2'(A_2959, B_2958), A_2959))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38643])).
% 22.41/13.18  tff(c_38659, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38555, c_38656])).
% 22.41/13.18  tff(c_38668, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_38659])).
% 22.41/13.18  tff(c_34026, plain, (![A_2482]: (~r2_hidden(A_2482, k6_partfun1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_249])).
% 22.41/13.18  tff(c_34031, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_34026])).
% 22.41/13.18  tff(c_38100, plain, (k6_partfun1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_38087, c_34031])).
% 22.41/13.18  tff(c_34230, plain, (![A_43]: (v4_relat_1(k6_partfun1(A_43), A_43))), inference(resolution, [status(thm)], [c_50, c_34204])).
% 22.41/13.18  tff(c_38381, plain, (![B_2913, A_2914]: (k1_relat_1(B_2913)=A_2914 | ~v1_partfun1(B_2913, A_2914) | ~v4_relat_1(B_2913, A_2914) | ~v1_relat_1(B_2913))), inference(cnfTransformation, [status(thm)], [f_109])).
% 22.41/13.18  tff(c_38387, plain, (![A_43]: (k1_relat_1(k6_partfun1(A_43))=A_43 | ~v1_partfun1(k6_partfun1(A_43), A_43) | ~v1_relat_1(k6_partfun1(A_43)))), inference(resolution, [status(thm)], [c_34230, c_38381])).
% 22.41/13.18  tff(c_38400, plain, (![A_2915]: (k1_relat_1(k6_partfun1(A_2915))=A_2915)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_48, c_38387])).
% 22.41/13.18  tff(c_38412, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_38100, c_38400])).
% 22.41/13.18  tff(c_34064, plain, (![A_2485, A_2486]: (~r2_hidden(A_2485, '#skF_2'(A_2486, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_241])).
% 22.41/13.18  tff(c_34073, plain, (![A_2487]: ('#skF_2'(A_2487, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_34064])).
% 22.41/13.18  tff(c_34087, plain, (![A_2487]: (v4_relat_1(k1_xboole_0, A_2487))), inference(superposition, [status(thm), theory('equality')], [c_34073, c_58])).
% 22.41/13.18  tff(c_38096, plain, (![A_2487]: (v4_relat_1('#skF_6', A_2487))), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_34087])).
% 22.41/13.18  tff(c_38384, plain, (![A_2487]: (k1_relat_1('#skF_6')=A_2487 | ~v1_partfun1('#skF_6', A_2487) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_38096, c_38381])).
% 22.41/13.18  tff(c_38393, plain, (![A_2487]: (k1_relat_1('#skF_6')=A_2487 | ~v1_partfun1('#skF_6', A_2487))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_38384])).
% 22.41/13.18  tff(c_38428, plain, (![A_2487]: (A_2487='#skF_6' | ~v1_partfun1('#skF_6', A_2487))), inference(demodulation, [status(thm), theory('equality')], [c_38412, c_38393])).
% 22.41/13.18  tff(c_38672, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_38668, c_38428])).
% 22.41/13.18  tff(c_38680, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_38672, c_92])).
% 22.41/13.18  tff(c_38107, plain, (![A_5]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_38087, c_16])).
% 22.41/13.18  tff(c_38634, plain, (![B_2955, A_2957]: (B_2955='#skF_6' | v1_partfun1('#skF_6', A_2957) | ~v1_funct_2('#skF_6', A_2957, B_2955) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_38107, c_38630])).
% 22.41/13.18  tff(c_38767, plain, (![B_2964, A_2965]: (B_2964='#skF_6' | v1_partfun1('#skF_6', A_2965) | ~v1_funct_2('#skF_6', A_2965, B_2964))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_38634])).
% 22.41/13.18  tff(c_38780, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_38680, c_38767])).
% 22.41/13.18  tff(c_39809, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_38780])).
% 22.41/13.18  tff(c_39815, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_39809, c_38428])).
% 22.41/13.18  tff(c_38677, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_38672, c_34180])).
% 22.41/13.18  tff(c_40075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38109, c_38105, c_39815, c_38677])).
% 22.41/13.18  tff(c_40076, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_38780])).
% 22.41/13.18  tff(c_40370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38109, c_38108, c_40076, c_38677])).
% 22.41/13.18  tff(c_40371, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_38659])).
% 22.41/13.18  tff(c_40379, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_40371, c_92])).
% 22.41/13.18  tff(c_40465, plain, (![B_3087, A_3088]: (B_3087='#skF_6' | v1_partfun1('#skF_6', A_3088) | ~v1_funct_2('#skF_6', A_3088, B_3087))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_38634])).
% 22.41/13.18  tff(c_40478, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(resolution, [status(thm)], [c_40379, c_40465])).
% 22.41/13.18  tff(c_41656, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_40478])).
% 22.41/13.18  tff(c_41662, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_41656, c_38428])).
% 22.41/13.18  tff(c_40376, plain, (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_40371, c_34180])).
% 22.41/13.18  tff(c_41970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38109, c_38105, c_41662, c_40376])).
% 22.41/13.18  tff(c_41971, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_40478])).
% 22.41/13.18  tff(c_42245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38109, c_38108, c_41971, c_40376])).
% 22.41/13.18  tff(c_42248, plain, (![A_3217]: (~r2_hidden(A_3217, '#skF_6'))), inference(splitRight, [status(thm)], [c_268])).
% 22.41/13.18  tff(c_42253, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_34, c_42248])).
% 22.41/13.18  tff(c_34069, plain, (![A_2486]: ('#skF_2'(A_2486, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_34064])).
% 22.41/13.18  tff(c_42389, plain, (![A_3226]: ('#skF_2'(A_3226, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_34069])).
% 22.41/13.18  tff(c_42397, plain, (![A_3226]: (v1_funct_2('#skF_6', A_3226, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_42389, c_52])).
% 22.41/13.18  tff(c_42261, plain, (![A_2486]: ('#skF_2'(A_2486, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_34069])).
% 22.41/13.18  tff(c_42271, plain, (![A_5]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_16])).
% 22.41/13.18  tff(c_43013, plain, (![B_3325, C_3326, A_3327]: (B_3325='#skF_6' | v1_partfun1(C_3326, A_3327) | ~v1_funct_2(C_3326, A_3327, B_3325) | ~m1_subset_1(C_3326, k1_zfmisc_1(k2_zfmisc_1(A_3327, B_3325))) | ~v1_funct_1(C_3326))), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_68])).
% 22.41/13.18  tff(c_43020, plain, (![B_3325, A_3327]: (B_3325='#skF_6' | v1_partfun1('#skF_6', A_3327) | ~v1_funct_2('#skF_6', A_3327, B_3325) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_42271, c_43013])).
% 22.41/13.18  tff(c_53229, plain, (![B_4010, A_4011]: (B_4010='#skF_6' | v1_partfun1('#skF_6', A_4011) | ~v1_funct_2('#skF_6', A_4011, B_4010))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_43020])).
% 22.41/13.18  tff(c_53247, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_117, c_53229])).
% 22.41/13.18  tff(c_53286, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_53247])).
% 22.41/13.18  tff(c_42264, plain, (k6_partfun1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_34031])).
% 22.41/13.18  tff(c_42417, plain, (![C_3227, A_3228, B_3229]: (v4_relat_1(C_3227, A_3228) | ~m1_subset_1(C_3227, k1_zfmisc_1(k2_zfmisc_1(A_3228, B_3229))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.41/13.18  tff(c_42438, plain, (![A_43]: (v4_relat_1(k6_partfun1(A_43), A_43))), inference(resolution, [status(thm)], [c_50, c_42417])).
% 22.41/13.18  tff(c_42616, plain, (![B_3263, A_3264]: (k1_relat_1(B_3263)=A_3264 | ~v1_partfun1(B_3263, A_3264) | ~v4_relat_1(B_3263, A_3264) | ~v1_relat_1(B_3263))), inference(cnfTransformation, [status(thm)], [f_109])).
% 22.41/13.18  tff(c_42619, plain, (![A_43]: (k1_relat_1(k6_partfun1(A_43))=A_43 | ~v1_partfun1(k6_partfun1(A_43), A_43) | ~v1_relat_1(k6_partfun1(A_43)))), inference(resolution, [status(thm)], [c_42438, c_42616])).
% 22.41/13.18  tff(c_42635, plain, (![A_3265]: (k1_relat_1(k6_partfun1(A_3265))=A_3265)), inference(demodulation, [status(thm), theory('equality')], [c_236, c_48, c_42619])).
% 22.41/13.18  tff(c_42647, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_42264, c_42635])).
% 22.41/13.18  tff(c_42260, plain, (![A_2487]: (v4_relat_1('#skF_6', A_2487))), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_34087])).
% 22.41/13.18  tff(c_42622, plain, (![A_2487]: (k1_relat_1('#skF_6')=A_2487 | ~v1_partfun1('#skF_6', A_2487) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_42260, c_42616])).
% 22.41/13.18  tff(c_42631, plain, (![A_2487]: (k1_relat_1('#skF_6')=A_2487 | ~v1_partfun1('#skF_6', A_2487))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_42622])).
% 22.41/13.18  tff(c_42663, plain, (![A_2487]: (A_2487='#skF_6' | ~v1_partfun1('#skF_6', A_2487))), inference(demodulation, [status(thm), theory('equality')], [c_42647, c_42631])).
% 22.41/13.18  tff(c_53290, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_53286, c_42663])).
% 22.41/13.18  tff(c_53293, plain, (~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_53290, c_33993])).
% 22.41/13.18  tff(c_34107, plain, (![A_2490, B_2491]: (~r2_hidden(A_2490, '#skF_2'(k1_xboole_0, B_2491)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_243])).
% 22.41/13.18  tff(c_34119, plain, (![B_2492]: ('#skF_2'(k1_xboole_0, B_2492)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_34107])).
% 22.41/13.18  tff(c_34130, plain, (![B_2492]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_2492))), inference(superposition, [status(thm), theory('equality')], [c_34119, c_52])).
% 22.41/13.18  tff(c_42257, plain, (![B_2492]: (v1_funct_2('#skF_6', '#skF_6', B_2492))), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_34130])).
% 22.41/13.18  tff(c_34115, plain, (![B_2491]: ('#skF_2'(k1_xboole_0, B_2491)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_34107])).
% 22.41/13.18  tff(c_42258, plain, (![B_2491]: ('#skF_2'('#skF_6', B_2491)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_34115])).
% 22.41/13.18  tff(c_43147, plain, (![B_3335, A_3336]: (B_3335='#skF_6' | v1_partfun1('#skF_6', A_3336) | ~v1_funct_2('#skF_6', A_3336, B_3335))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_43020])).
% 22.41/13.18  tff(c_43165, plain, (u1_struct_0('#skF_4')='#skF_6' | v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_117, c_43147])).
% 22.41/13.18  tff(c_43166, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_43165])).
% 22.41/13.18  tff(c_43208, plain, (u1_struct_0('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_43166, c_42663])).
% 22.41/13.18  tff(c_44926, plain, (![D_3453, A_3454, B_3455]: (v5_pre_topc(D_3453, A_3454, g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455))) | ~v5_pre_topc(D_3453, A_3454, B_3455) | ~m1_subset_1(D_3453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))))) | ~v1_funct_2(D_3453, u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))) | ~m1_subset_1(D_3453, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3454), u1_struct_0(B_3455)))) | ~v1_funct_2(D_3453, u1_struct_0(A_3454), u1_struct_0(B_3455)) | ~v1_funct_1(D_3453) | ~l1_pre_topc(B_3455) | ~v2_pre_topc(B_3455) | ~l1_pre_topc(A_3454) | ~v2_pre_topc(A_3454))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.18  tff(c_44950, plain, (![A_3454, B_3455]: (v5_pre_topc('#skF_2'(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))), A_3454, g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))), A_3454, B_3455) | ~v1_funct_2('#skF_2'(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))), u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3454), u1_struct_0(B_3455)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455)))), u1_struct_0(A_3454), u1_struct_0(B_3455)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_3454), u1_struct_0(g1_pre_topc(u1_struct_0(B_3455), u1_pre_topc(B_3455))))) | ~l1_pre_topc(B_3455) | ~v2_pre_topc(B_3455) | ~l1_pre_topc(A_3454) | ~v2_pre_topc(A_3454))), inference(resolution, [status(thm)], [c_62, c_44926])).
% 22.41/13.18  tff(c_45438, plain, (![A_3508, B_3509]: (v5_pre_topc('#skF_2'(u1_struct_0(A_3508), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), A_3508, g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_3508), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), A_3508, B_3509) | ~m1_subset_1('#skF_2'(u1_struct_0(A_3508), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3508), u1_struct_0(B_3509)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_3508), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), u1_struct_0(A_3508), u1_struct_0(B_3509)) | ~l1_pre_topc(B_3509) | ~v2_pre_topc(B_3509) | ~l1_pre_topc(A_3508) | ~v2_pre_topc(A_3508))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_44950])).
% 22.41/13.18  tff(c_45448, plain, (![B_3509]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), '#skF_3', g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509))) | ~v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), '#skF_3', B_3509) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_3509)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3509), u1_pre_topc(B_3509)))), u1_struct_0('#skF_3'), u1_struct_0(B_3509)) | ~l1_pre_topc(B_3509) | ~v2_pre_topc(B_3509) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43208, c_45438])).
% 22.41/13.18  tff(c_46362, plain, (![B_3584]: (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_3584), u1_pre_topc(B_3584))) | ~v5_pre_topc('#skF_6', '#skF_3', B_3584) | ~l1_pre_topc(B_3584) | ~v2_pre_topc(B_3584))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_42257, c_42258, c_43208, c_43208, c_42271, c_42258, c_43208, c_42258, c_43208, c_42258, c_43208, c_45448])).
% 22.41/13.18  tff(c_42269, plain, (![B_4]: (k2_zfmisc_1('#skF_6', B_4)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_14])).
% 22.41/13.18  tff(c_42247, plain, (v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitRight, [status(thm)], [c_268])).
% 22.41/13.18  tff(c_42268, plain, (![A_24]: (r2_hidden('#skF_1'(A_24), A_24) | A_24='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_34])).
% 22.41/13.18  tff(c_42584, plain, (![A_3256, B_3257, A_3258]: (~v1_xboole_0(k2_zfmisc_1(A_3256, B_3257)) | ~r2_hidden(A_3258, '#skF_2'(A_3256, B_3257)))), inference(resolution, [status(thm)], [c_62, c_239])).
% 22.41/13.18  tff(c_42600, plain, (![A_3259, B_3260]: (~v1_xboole_0(k2_zfmisc_1(A_3259, B_3260)) | '#skF_2'(A_3259, B_3260)='#skF_6')), inference(resolution, [status(thm)], [c_42268, c_42584])).
% 22.41/13.18  tff(c_42610, plain, ('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))='#skF_6'), inference(resolution, [status(thm)], [c_42247, c_42600])).
% 22.41/13.18  tff(c_43029, plain, (![B_45, A_44]: (B_45='#skF_6' | v1_partfun1('#skF_2'(A_44, B_45), A_44) | ~v1_funct_2('#skF_2'(A_44, B_45), A_44, B_45) | ~v1_funct_1('#skF_2'(A_44, B_45)))), inference(resolution, [status(thm)], [c_62, c_43013])).
% 22.41/13.18  tff(c_43043, plain, (![B_3328, A_3329]: (B_3328='#skF_6' | v1_partfun1('#skF_2'(A_3329, B_3328), A_3329))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_43029])).
% 22.41/13.18  tff(c_43049, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6' | v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_42610, c_43043])).
% 22.41/13.18  tff(c_43077, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(splitLeft, [status(thm)], [c_43049])).
% 22.41/13.18  tff(c_43110, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_43077, c_42663])).
% 22.41/13.18  tff(c_43210, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_43208, c_43110])).
% 22.41/13.18  tff(c_44986, plain, (![D_3459, A_3460, B_3461]: (v5_pre_topc(D_3459, g1_pre_topc(u1_struct_0(A_3460), u1_pre_topc(A_3460)), B_3461) | ~v5_pre_topc(D_3459, A_3460, B_3461) | ~m1_subset_1(D_3459, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3460), u1_pre_topc(A_3460))), u1_struct_0(B_3461)))) | ~v1_funct_2(D_3459, u1_struct_0(g1_pre_topc(u1_struct_0(A_3460), u1_pre_topc(A_3460))), u1_struct_0(B_3461)) | ~m1_subset_1(D_3459, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3460), u1_struct_0(B_3461)))) | ~v1_funct_2(D_3459, u1_struct_0(A_3460), u1_struct_0(B_3461)) | ~v1_funct_1(D_3459) | ~l1_pre_topc(B_3461) | ~v2_pre_topc(B_3461) | ~l1_pre_topc(A_3460) | ~v2_pre_topc(A_3460))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.18  tff(c_44995, plain, (![D_3459, B_3461]: (v5_pre_topc(D_3459, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), B_3461) | ~v5_pre_topc(D_3459, '#skF_3', B_3461) | ~m1_subset_1(D_3459, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_3'))), u1_struct_0(B_3461)))) | ~v1_funct_2(D_3459, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), u1_struct_0(B_3461)) | ~m1_subset_1(D_3459, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_3461)))) | ~v1_funct_2(D_3459, u1_struct_0('#skF_3'), u1_struct_0(B_3461)) | ~v1_funct_1(D_3459) | ~l1_pre_topc(B_3461) | ~v2_pre_topc(B_3461) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_43208, c_44986])).
% 22.41/13.18  tff(c_45244, plain, (![D_3481, B_3482]: (v5_pre_topc(D_3481, g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), B_3482) | ~v5_pre_topc(D_3481, '#skF_3', B_3482) | ~m1_subset_1(D_3481, k1_zfmisc_1('#skF_6')) | ~v1_funct_2(D_3481, '#skF_6', u1_struct_0(B_3482)) | ~v1_funct_1(D_3481) | ~l1_pre_topc(B_3482) | ~v2_pre_topc(B_3482))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_43208, c_42269, c_43208, c_43210, c_43208, c_42269, c_43210, c_43208, c_44995])).
% 22.41/13.18  tff(c_43211, plain, (~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_43208, c_33993])).
% 22.41/13.18  tff(c_45251, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_6', '#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_45244, c_43211])).
% 22.41/13.18  tff(c_45257, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_42257, c_42271, c_45251])).
% 22.41/13.18  tff(c_45384, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_45257])).
% 22.41/13.18  tff(c_45387, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_45384])).
% 22.41/13.18  tff(c_45391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_45387])).
% 22.41/13.18  tff(c_45392, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_45257])).
% 22.41/13.18  tff(c_45510, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_45392])).
% 22.41/13.18  tff(c_46368, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_46362, c_45510])).
% 22.41/13.18  tff(c_46382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_33994, c_46368])).
% 22.41/13.18  tff(c_46383, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_45392])).
% 22.41/13.18  tff(c_46387, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34171, c_46383])).
% 22.41/13.18  tff(c_46391, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_46387])).
% 22.41/13.18  tff(c_46392, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_43165])).
% 22.41/13.18  tff(c_46394, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_46392, c_33993])).
% 22.41/13.18  tff(c_43135, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_43110, c_34171])).
% 22.41/13.18  tff(c_51089, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_43135])).
% 22.41/13.18  tff(c_51092, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34171, c_51089])).
% 22.41/13.18  tff(c_51096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_51092])).
% 22.41/13.18  tff(c_51098, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_43135])).
% 22.41/13.18  tff(c_43141, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_6'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_43110, c_74])).
% 22.41/13.18  tff(c_51268, plain, (m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), k1_zfmisc_1(k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_51098, c_43141])).
% 22.41/13.18  tff(c_51341, plain, (![A_3929]: (m1_subset_1(A_3929, k1_zfmisc_1('#skF_6')) | ~r2_hidden(A_3929, u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))))), inference(resolution, [status(thm)], [c_51268, c_18])).
% 22.41/13.18  tff(c_51346, plain, (m1_subset_1('#skF_1'(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), k1_zfmisc_1('#skF_6')) | u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(resolution, [status(thm)], [c_42268, c_51341])).
% 22.41/13.18  tff(c_51788, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))='#skF_6'), inference(splitLeft, [status(thm)], [c_51346])).
% 22.41/13.18  tff(c_51892, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_6')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_51788, c_76])).
% 22.41/13.18  tff(c_51965, plain, (v2_pre_topc(g1_pre_topc('#skF_6', '#skF_6')) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_51098, c_43110, c_51892])).
% 22.41/13.18  tff(c_51969, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_51965])).
% 22.41/13.18  tff(c_51972, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_51969])).
% 22.41/13.19  tff(c_51976, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_51972])).
% 22.41/13.19  tff(c_51978, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_51965])).
% 22.41/13.19  tff(c_46435, plain, (![D_3585, A_3586, B_3587]: (v5_pre_topc(D_3585, g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586)), B_3587) | ~v5_pre_topc(D_3585, A_3586, B_3587) | ~m1_subset_1(D_3585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)))) | ~v1_funct_2(D_3585, u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)) | ~m1_subset_1(D_3585, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3586), u1_struct_0(B_3587)))) | ~v1_funct_2(D_3585, u1_struct_0(A_3586), u1_struct_0(B_3587)) | ~v1_funct_1(D_3585) | ~l1_pre_topc(B_3587) | ~v2_pre_topc(B_3587) | ~l1_pre_topc(A_3586) | ~v2_pre_topc(A_3586))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.19  tff(c_46462, plain, (![A_3586, B_3587]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)), g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586)), B_3587) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)), A_3586, B_3587) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)), u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3586), u1_struct_0(B_3587)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587)), u1_struct_0(A_3586), u1_struct_0(B_3587)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3586), u1_pre_topc(A_3586))), u1_struct_0(B_3587))) | ~l1_pre_topc(B_3587) | ~v2_pre_topc(B_3587) | ~l1_pre_topc(A_3586) | ~v2_pre_topc(A_3586))), inference(resolution, [status(thm)], [c_62, c_46435])).
% 22.41/13.19  tff(c_50789, plain, (![A_3879, B_3880]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0(B_3880)), g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879)), B_3880) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0(B_3880)), A_3879, B_3880) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0(B_3880)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3879), u1_struct_0(B_3880)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0(B_3880)), u1_struct_0(A_3879), u1_struct_0(B_3880)) | ~l1_pre_topc(B_3880) | ~v2_pre_topc(B_3880) | ~l1_pre_topc(A_3879) | ~v2_pre_topc(A_3879))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_46462])).
% 22.41/13.19  tff(c_50799, plain, (![A_3879]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0('#skF_4')), g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879)), '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0('#skF_4')), A_3879, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3879), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879))), u1_struct_0('#skF_4')), u1_struct_0(A_3879), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_3879) | ~v2_pre_topc(A_3879))), inference(superposition, [status(thm), theory('equality')], [c_46392, c_50789])).
% 22.41/13.19  tff(c_50819, plain, (![A_3879]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_3879), u1_pre_topc(A_3879)), '#skF_4') | ~v5_pre_topc('#skF_6', A_3879, '#skF_4') | ~l1_pre_topc(A_3879) | ~v2_pre_topc(A_3879))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_42397, c_42261, c_46392, c_46392, c_42271, c_42261, c_46392, c_42261, c_46392, c_42261, c_46392, c_50799])).
% 22.41/13.19  tff(c_51841, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), '#skF_6'), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_51788, c_50819])).
% 22.41/13.19  tff(c_51927, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', '#skF_6'), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_51098, c_43110, c_51841])).
% 22.41/13.19  tff(c_52480, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', '#skF_6'), '#skF_4') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_51978, c_51927])).
% 22.41/13.19  tff(c_52481, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_52480])).
% 22.41/13.19  tff(c_52484, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50819, c_52481])).
% 22.41/13.19  tff(c_52488, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_33994, c_52484])).
% 22.41/13.19  tff(c_52490, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_52480])).
% 22.41/13.19  tff(c_42272, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42253, c_42253, c_12])).
% 22.41/13.19  tff(c_49976, plain, (![D_3798, A_3799, B_3800]: (v5_pre_topc(D_3798, A_3799, g1_pre_topc(u1_struct_0(B_3800), u1_pre_topc(B_3800))) | ~v5_pre_topc(D_3798, A_3799, B_3800) | ~m1_subset_1(D_3798, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799), u1_struct_0(g1_pre_topc(u1_struct_0(B_3800), u1_pre_topc(B_3800)))))) | ~v1_funct_2(D_3798, u1_struct_0(A_3799), u1_struct_0(g1_pre_topc(u1_struct_0(B_3800), u1_pre_topc(B_3800)))) | ~m1_subset_1(D_3798, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799), u1_struct_0(B_3800)))) | ~v1_funct_2(D_3798, u1_struct_0(A_3799), u1_struct_0(B_3800)) | ~v1_funct_1(D_3798) | ~l1_pre_topc(B_3800) | ~v2_pre_topc(B_3800) | ~l1_pre_topc(A_3799) | ~v2_pre_topc(A_3799))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.19  tff(c_49982, plain, (![D_3798, A_3799]: (v5_pre_topc(D_3798, A_3799, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc(D_3798, A_3799, '#skF_4') | ~m1_subset_1(D_3798, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))) | ~v1_funct_2(D_3798, u1_struct_0(A_3799), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~m1_subset_1(D_3798, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3799), u1_struct_0('#skF_4')))) | ~v1_funct_2(D_3798, u1_struct_0(A_3799), u1_struct_0('#skF_4')) | ~v1_funct_1(D_3798) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_3799) | ~v2_pre_topc(A_3799))), inference(superposition, [status(thm), theory('equality')], [c_46392, c_49976])).
% 22.41/13.19  tff(c_53098, plain, (![D_4005, A_4006]: (v5_pre_topc(D_4005, A_4006, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc(D_4005, A_4006, '#skF_4') | ~m1_subset_1(D_4005, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4006), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))))) | ~v1_funct_2(D_4005, u1_struct_0(A_4006), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~m1_subset_1(D_4005, k1_zfmisc_1('#skF_6')) | ~v1_funct_2(D_4005, u1_struct_0(A_4006), '#skF_6') | ~v1_funct_1(D_4005) | ~l1_pre_topc(A_4006) | ~v2_pre_topc(A_4006))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_46392, c_42272, c_46392, c_46392, c_46392, c_49982])).
% 22.41/13.19  tff(c_53120, plain, (![A_4006]: (v5_pre_topc('#skF_6', A_4006, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_4006, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_4006), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0(A_4006), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc(A_4006) | ~v2_pre_topc(A_4006))), inference(resolution, [status(thm)], [c_42271, c_53098])).
% 22.41/13.19  tff(c_53147, plain, (![A_4007]: (v5_pre_topc('#skF_6', A_4007, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_4007, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_4007), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~l1_pre_topc(A_4007) | ~v2_pre_topc(A_4007))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_42397, c_42271, c_53120])).
% 22.41/13.19  tff(c_53153, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~v1_funct_2('#skF_6', '#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_43110, c_53147])).
% 22.41/13.19  tff(c_53161, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_51978, c_51098, c_42257, c_52490, c_53153])).
% 22.41/13.19  tff(c_53163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46394, c_53161])).
% 22.41/13.19  tff(c_53164, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(splitRight, [status(thm)], [c_43049])).
% 22.41/13.19  tff(c_57373, plain, (![D_4242, A_4243, B_4244]: (v5_pre_topc(D_4242, A_4243, g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244))) | ~v5_pre_topc(D_4242, A_4243, B_4244) | ~m1_subset_1(D_4242, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))))) | ~v1_funct_2(D_4242, u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))) | ~m1_subset_1(D_4242, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4243), u1_struct_0(B_4244)))) | ~v1_funct_2(D_4242, u1_struct_0(A_4243), u1_struct_0(B_4244)) | ~v1_funct_1(D_4242) | ~l1_pre_topc(B_4244) | ~v2_pre_topc(B_4244) | ~l1_pre_topc(A_4243) | ~v2_pre_topc(A_4243))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.19  tff(c_57400, plain, (![A_4243, B_4244]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))), A_4243, g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))), A_4243, B_4244) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))), u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4243), u1_struct_0(B_4244)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244)))), u1_struct_0(A_4243), u1_struct_0(B_4244)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_4243), u1_struct_0(g1_pre_topc(u1_struct_0(B_4244), u1_pre_topc(B_4244))))) | ~l1_pre_topc(B_4244) | ~v2_pre_topc(B_4244) | ~l1_pre_topc(A_4243) | ~v2_pre_topc(A_4243))), inference(resolution, [status(thm)], [c_62, c_57373])).
% 22.41/13.19  tff(c_57857, plain, (![A_4291, B_4292]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), A_4291, g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), A_4291, B_4292) | ~m1_subset_1('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4291), u1_struct_0(B_4292)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), u1_struct_0(A_4291), u1_struct_0(B_4292)) | ~l1_pre_topc(B_4292) | ~v2_pre_topc(B_4292) | ~l1_pre_topc(A_4291) | ~v2_pre_topc(A_4291))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_57400])).
% 22.41/13.19  tff(c_57871, plain, (![A_4291]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_4291, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_4291, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(A_4291), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4291), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4291), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_4291), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_4291) | ~v2_pre_topc(A_4291))), inference(superposition, [status(thm), theory('equality')], [c_53164, c_57857])).
% 22.41/13.19  tff(c_57889, plain, (![A_4291]: (v5_pre_topc('#skF_6', A_4291, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_4291, '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0(A_4291), u1_struct_0('#skF_4')) | ~l1_pre_topc(A_4291) | ~v2_pre_topc(A_4291))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_42261, c_53164, c_42271, c_42261, c_42261, c_53164, c_42261, c_53164, c_57871])).
% 22.41/13.19  tff(c_42305, plain, (![A_3219, B_3220]: (v1_pre_topc(g1_pre_topc(A_3219, B_3220)) | ~m1_subset_1(B_3220, k1_zfmisc_1(k1_zfmisc_1(A_3219))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 22.41/13.19  tff(c_42309, plain, (![A_53]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_53), u1_pre_topc(A_53))) | ~l1_pre_topc(A_53))), inference(resolution, [status(thm)], [c_74, c_42305])).
% 22.41/13.19  tff(c_53214, plain, (v1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_53164, c_42309])).
% 22.41/13.19  tff(c_57445, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_53214])).
% 22.41/13.19  tff(c_57448, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_34171, c_57445])).
% 22.41/13.19  tff(c_57452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_57448])).
% 22.41/13.19  tff(c_57454, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_53214])).
% 22.41/13.19  tff(c_53220, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_53164, c_76])).
% 22.41/13.19  tff(c_60580, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_57454, c_53220])).
% 22.41/13.19  tff(c_60581, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_60580])).
% 22.41/13.19  tff(c_60584, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_76, c_60581])).
% 22.41/13.19  tff(c_60588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_60584])).
% 22.41/13.19  tff(c_60590, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_60580])).
% 22.41/13.19  tff(c_57281, plain, (![D_4235, A_4236, B_4237]: (v5_pre_topc(D_4235, A_4236, B_4237) | ~v5_pre_topc(D_4235, A_4236, g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237))) | ~m1_subset_1(D_4235, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))))) | ~v1_funct_2(D_4235, u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))) | ~m1_subset_1(D_4235, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4236), u1_struct_0(B_4237)))) | ~v1_funct_2(D_4235, u1_struct_0(A_4236), u1_struct_0(B_4237)) | ~v1_funct_1(D_4235) | ~l1_pre_topc(B_4237) | ~v2_pre_topc(B_4237) | ~l1_pre_topc(A_4236) | ~v2_pre_topc(A_4236))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.19  tff(c_57308, plain, (![A_4236, B_4237]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))), A_4236, B_4237) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))), A_4236, g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))), u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4236), u1_struct_0(B_4237)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237)))), u1_struct_0(A_4236), u1_struct_0(B_4237)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_4236), u1_struct_0(g1_pre_topc(u1_struct_0(B_4237), u1_pre_topc(B_4237))))) | ~l1_pre_topc(B_4237) | ~v2_pre_topc(B_4237) | ~l1_pre_topc(A_4236) | ~v2_pre_topc(A_4236))), inference(resolution, [status(thm)], [c_62, c_57281])).
% 22.41/13.19  tff(c_58140, plain, (![A_4325, B_4326]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4325), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), A_4325, B_4326) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4325), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), A_4325, g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_4325), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4325), u1_struct_0(B_4326)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4325), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), u1_struct_0(A_4325), u1_struct_0(B_4326)) | ~l1_pre_topc(B_4326) | ~v2_pre_topc(B_4326) | ~l1_pre_topc(A_4325) | ~v2_pre_topc(A_4325))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_57308])).
% 22.41/13.19  tff(c_58142, plain, (![B_4326]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), '#skF_3', B_4326) | ~v5_pre_topc('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), '#skF_3', g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326))) | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_4326)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4326), u1_pre_topc(B_4326)))), u1_struct_0('#skF_3'), u1_struct_0(B_4326)) | ~l1_pre_topc(B_4326) | ~v2_pre_topc(B_4326) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53290, c_58140])).
% 22.41/13.19  tff(c_58462, plain, (![B_4360]: (v5_pre_topc('#skF_6', '#skF_3', B_4360) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_4360), u1_pre_topc(B_4360))) | ~l1_pre_topc(B_4360) | ~v2_pre_topc(B_4360))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_42257, c_42258, c_53290, c_53290, c_42271, c_42258, c_53290, c_53290, c_42258, c_42258, c_53290, c_58142])).
% 22.41/13.19  tff(c_58471, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_53164, c_58462])).
% 22.41/13.19  tff(c_58477, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_57454, c_58471])).
% 22.41/13.19  tff(c_61379, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(demodulation, [status(thm), theory('equality')], [c_60590, c_58477])).
% 22.41/13.19  tff(c_61380, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))))), inference(splitLeft, [status(thm)], [c_61379])).
% 22.41/13.19  tff(c_57859, plain, (![B_4292]: (v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), '#skF_3', g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292))) | ~v5_pre_topc('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), '#skF_3', B_4292) | ~m1_subset_1('#skF_2'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_4292)))) | ~v1_funct_2('#skF_2'(u1_struct_0('#skF_3'), u1_struct_0(g1_pre_topc(u1_struct_0(B_4292), u1_pre_topc(B_4292)))), u1_struct_0('#skF_3'), u1_struct_0(B_4292)) | ~l1_pre_topc(B_4292) | ~v2_pre_topc(B_4292) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53290, c_57857])).
% 22.41/13.19  tff(c_57934, plain, (![B_4298]: (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0(B_4298), u1_pre_topc(B_4298))) | ~v5_pre_topc('#skF_6', '#skF_3', B_4298) | ~l1_pre_topc(B_4298) | ~v2_pre_topc(B_4298))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_42257, c_42258, c_53290, c_53290, c_42271, c_42258, c_53290, c_42258, c_53290, c_42258, c_53290, c_57859])).
% 22.41/13.19  tff(c_57940, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_53164, c_57934])).
% 22.41/13.19  tff(c_57944, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_57454, c_57940])).
% 22.41/13.19  tff(c_61382, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_60590, c_57944])).
% 22.41/13.19  tff(c_61383, plain, (~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_61380, c_61382])).
% 22.41/13.19  tff(c_61386, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_57889, c_61383])).
% 22.41/13.19  tff(c_61393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_42257, c_53290, c_33994, c_61386])).
% 22.41/13.19  tff(c_61394, plain, (v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_61379])).
% 22.41/13.19  tff(c_42880, plain, (![D_3312, B_3313, C_3314, A_3315]: (m1_subset_1(D_3312, k1_zfmisc_1(k2_zfmisc_1(B_3313, C_3314))) | ~r1_tarski(k1_relat_1(D_3312), B_3313) | ~m1_subset_1(D_3312, k1_zfmisc_1(k2_zfmisc_1(A_3315, C_3314))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 22.41/13.19  tff(c_42895, plain, (![A_44, B_45, B_3313]: (m1_subset_1('#skF_2'(A_44, B_45), k1_zfmisc_1(k2_zfmisc_1(B_3313, B_45))) | ~r1_tarski(k1_relat_1('#skF_2'(A_44, B_45)), B_3313))), inference(resolution, [status(thm)], [c_62, c_42880])).
% 22.41/13.19  tff(c_53248, plain, (![D_4012, A_4013, B_4014]: (v5_pre_topc(D_4012, g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013)), B_4014) | ~v5_pre_topc(D_4012, A_4013, B_4014) | ~m1_subset_1(D_4012, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)))) | ~v1_funct_2(D_4012, u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)) | ~m1_subset_1(D_4012, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4013), u1_struct_0(B_4014)))) | ~v1_funct_2(D_4012, u1_struct_0(A_4013), u1_struct_0(B_4014)) | ~v1_funct_1(D_4012) | ~l1_pre_topc(B_4014) | ~v2_pre_topc(B_4014) | ~l1_pre_topc(A_4013) | ~v2_pre_topc(A_4013))), inference(cnfTransformation, [status(thm)], [f_192])).
% 22.41/13.19  tff(c_53269, plain, (![A_4013, B_4014]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)), g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013)), B_4014) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)), A_4013, B_4014) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)), u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4013), u1_struct_0(B_4014)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014)), u1_struct_0(A_4013), u1_struct_0(B_4014)) | ~v1_funct_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4013), u1_pre_topc(A_4013))), u1_struct_0(B_4014))) | ~l1_pre_topc(B_4014) | ~v2_pre_topc(B_4014) | ~l1_pre_topc(A_4013) | ~v2_pre_topc(A_4013))), inference(resolution, [status(thm)], [c_62, c_53248])).
% 22.41/13.19  tff(c_57675, plain, (![A_4270, B_4271]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270), u1_pre_topc(A_4270))), u1_struct_0(B_4271)), g1_pre_topc(u1_struct_0(A_4270), u1_pre_topc(A_4270)), B_4271) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270), u1_pre_topc(A_4270))), u1_struct_0(B_4271)), A_4270, B_4271) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270), u1_pre_topc(A_4270))), u1_struct_0(B_4271)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4270), u1_struct_0(B_4271)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4270), u1_pre_topc(A_4270))), u1_struct_0(B_4271)), u1_struct_0(A_4270), u1_struct_0(B_4271)) | ~l1_pre_topc(B_4271) | ~v2_pre_topc(B_4271) | ~l1_pre_topc(A_4270) | ~v2_pre_topc(A_4270))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_53269])).
% 22.41/13.19  tff(c_60593, plain, (![A_4446, B_4447]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(B_4447)), g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446)), B_4447) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(B_4447)), A_4446, B_4447) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(B_4447)), u1_struct_0(A_4446), u1_struct_0(B_4447)) | ~l1_pre_topc(B_4447) | ~v2_pre_topc(B_4447) | ~l1_pre_topc(A_4446) | ~v2_pre_topc(A_4446) | ~r1_tarski(k1_relat_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(B_4447))), u1_struct_0(A_4446)))), inference(resolution, [status(thm)], [c_42895, c_57675])).
% 22.41/13.19  tff(c_60616, plain, (![A_4446]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), '#skF_6'), g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_4446, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_4446), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_4446) | ~v2_pre_topc(A_4446) | ~r1_tarski(k1_relat_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4446), u1_pre_topc(A_4446))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), u1_struct_0(A_4446)))), inference(superposition, [status(thm), theory('equality')], [c_53164, c_60593])).
% 22.41/13.19  tff(c_62084, plain, (![A_4507]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_4507), u1_pre_topc(A_4507)), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_4507, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_4507) | ~v2_pre_topc(A_4507) | ~r1_tarski('#skF_6', u1_struct_0(A_4507)))), inference(demodulation, [status(thm), theory('equality')], [c_42647, c_42261, c_53164, c_60590, c_57454, c_42397, c_42261, c_53164, c_53164, c_42261, c_53164, c_42261, c_60616])).
% 22.41/13.19  tff(c_62097, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', '#skF_3', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_53290, c_62084])).
% 22.41/13.19  tff(c_62110, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_53290, c_108, c_106, c_61394, c_62097])).
% 22.41/13.19  tff(c_62112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53293, c_62110])).
% 22.41/13.19  tff(c_62113, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(splitRight, [status(thm)], [c_53247])).
% 22.41/13.19  tff(c_64649, plain, (![A_4711, B_4712]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0(B_4712)), g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711)), B_4712) | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0(B_4712)), A_4711, B_4712) | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0(B_4712)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4711), u1_struct_0(B_4712)))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0(B_4712)), u1_struct_0(A_4711), u1_struct_0(B_4712)) | ~l1_pre_topc(B_4712) | ~v2_pre_topc(B_4712) | ~l1_pre_topc(A_4711) | ~v2_pre_topc(A_4711))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_53269])).
% 22.41/13.19  tff(c_64664, plain, (![A_4711]: (v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0('#skF_4')), g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711)), '#skF_4') | ~v5_pre_topc('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0('#skF_4')), A_4711, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4711), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(g1_pre_topc(u1_struct_0(A_4711), u1_pre_topc(A_4711))), u1_struct_0('#skF_4')), u1_struct_0(A_4711), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_4711) | ~v2_pre_topc(A_4711))), inference(superposition, [status(thm), theory('equality')], [c_62113, c_64649])).
% 22.41/13.19  tff(c_65479, plain, (![A_4776]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_4776), u1_pre_topc(A_4776)), '#skF_4') | ~v5_pre_topc('#skF_6', A_4776, '#skF_4') | ~l1_pre_topc(A_4776) | ~v2_pre_topc(A_4776))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_42397, c_42261, c_62113, c_62113, c_42271, c_42261, c_62113, c_42261, c_62113, c_42261, c_62113, c_64664])).
% 22.41/13.19  tff(c_62115, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62113, c_53164])).
% 22.41/13.19  tff(c_64109, plain, (![D_4652, A_4653, B_4654]: (v5_pre_topc(D_4652, A_4653, g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654))) | ~v5_pre_topc(D_4652, A_4653, B_4654) | ~m1_subset_1(D_4652, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))))) | ~v1_funct_2(D_4652, u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))) | ~m1_subset_1(D_4652, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4653), u1_struct_0(B_4654)))) | ~v1_funct_2(D_4652, u1_struct_0(A_4653), u1_struct_0(B_4654)) | ~v1_funct_1(D_4652) | ~l1_pre_topc(B_4654) | ~v2_pre_topc(B_4654) | ~l1_pre_topc(A_4653) | ~v2_pre_topc(A_4653))), inference(cnfTransformation, [status(thm)], [f_221])).
% 22.41/13.19  tff(c_64133, plain, (![A_4653, B_4654]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))), A_4653, g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))), A_4653, B_4654) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))), u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))) | ~m1_subset_1('#skF_2'(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4653), u1_struct_0(B_4654)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654)))), u1_struct_0(A_4653), u1_struct_0(B_4654)) | ~v1_funct_1('#skF_2'(u1_struct_0(A_4653), u1_struct_0(g1_pre_topc(u1_struct_0(B_4654), u1_pre_topc(B_4654))))) | ~l1_pre_topc(B_4654) | ~v2_pre_topc(B_4654) | ~l1_pre_topc(A_4653) | ~v2_pre_topc(A_4653))), inference(resolution, [status(thm)], [c_62, c_64109])).
% 22.41/13.19  tff(c_64400, plain, (![A_4680, B_4681]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0(B_4681), u1_pre_topc(B_4681)))), A_4680, g1_pre_topc(u1_struct_0(B_4681), u1_pre_topc(B_4681))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0(B_4681), u1_pre_topc(B_4681)))), A_4680, B_4681) | ~m1_subset_1('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0(B_4681), u1_pre_topc(B_4681)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4680), u1_struct_0(B_4681)))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0(B_4681), u1_pre_topc(B_4681)))), u1_struct_0(A_4680), u1_struct_0(B_4681)) | ~l1_pre_topc(B_4681) | ~v2_pre_topc(B_4681) | ~l1_pre_topc(A_4680) | ~v2_pre_topc(A_4680))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_64133])).
% 22.41/13.19  tff(c_64412, plain, (![A_4680]: (v5_pre_topc('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_4680, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), A_4680, '#skF_4') | ~m1_subset_1('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_4680), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_2'(u1_struct_0(A_4680), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), u1_struct_0(A_4680), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(A_4680) | ~v2_pre_topc(A_4680))), inference(superposition, [status(thm), theory('equality')], [c_62113, c_64400])).
% 22.41/13.19  tff(c_64440, plain, (![A_4684]: (v5_pre_topc('#skF_6', A_4684, g1_pre_topc('#skF_6', u1_pre_topc('#skF_4'))) | ~v5_pre_topc('#skF_6', A_4684, '#skF_4') | ~l1_pre_topc(A_4684) | ~v2_pre_topc(A_4684))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_42397, c_42261, c_62113, c_62115, c_62113, c_42271, c_42261, c_62113, c_62115, c_42261, c_62115, c_62113, c_42261, c_62113, c_62115, c_62113, c_64412])).
% 22.41/13.19  tff(c_62116, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_62113, c_33993])).
% 22.41/13.19  tff(c_64450, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_64440, c_62116])).
% 22.41/13.19  tff(c_64608, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_64450])).
% 22.41/13.19  tff(c_64611, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_76, c_64608])).
% 22.41/13.19  tff(c_64615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_64611])).
% 22.41/13.19  tff(c_64616, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_64450])).
% 22.41/13.19  tff(c_64771, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_64616])).
% 22.41/13.19  tff(c_65485, plain, (~v5_pre_topc('#skF_6', '#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_65479, c_64771])).
% 22.41/13.19  tff(c_65499, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_106, c_33994, c_65485])).
% 22.41/13.19  tff(c_65500, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_64616])).
% 22.41/13.19  tff(c_65505, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_34171, c_65500])).
% 22.41/13.19  tff(c_65509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_65505])).
% 22.41/13.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.41/13.19  
% 22.41/13.19  Inference rules
% 22.41/13.19  ----------------------
% 22.41/13.19  #Ref     : 0
% 22.41/13.19  #Sup     : 12748
% 22.41/13.19  #Fact    : 0
% 22.41/13.19  #Define  : 0
% 22.41/13.19  #Split   : 233
% 22.41/13.19  #Chain   : 0
% 22.41/13.19  #Close   : 0
% 22.41/13.19  
% 22.41/13.19  Ordering : KBO
% 22.41/13.19  
% 22.41/13.19  Simplification rules
% 22.41/13.19  ----------------------
% 22.41/13.19  #Subsume      : 3169
% 22.41/13.19  #Demod        : 79313
% 22.41/13.19  #Tautology    : 3979
% 22.41/13.19  #SimpNegUnit  : 1036
% 22.41/13.19  #BackRed      : 510
% 22.41/13.19  
% 22.41/13.19  #Partial instantiations: 0
% 22.41/13.19  #Strategies tried      : 1
% 22.41/13.19  
% 22.41/13.19  Timing (in seconds)
% 22.41/13.19  ----------------------
% 22.41/13.19  Preprocessing        : 0.39
% 22.41/13.19  Parsing              : 0.21
% 22.41/13.19  CNF conversion       : 0.03
% 22.41/13.19  Main loop            : 11.86
% 22.41/13.19  Inferencing          : 2.65
% 22.41/13.19  Reduction            : 6.43
% 22.41/13.19  Demodulation         : 5.44
% 22.41/13.19  BG Simplification    : 0.24
% 22.41/13.19  Subsumption          : 2.02
% 22.41/13.19  Abstraction          : 0.41
% 22.41/13.19  MUC search           : 0.00
% 22.41/13.19  Cooper               : 0.00
% 22.41/13.19  Total                : 12.46
% 22.41/13.19  Index Insertion      : 0.00
% 22.41/13.19  Index Deletion       : 0.00
% 22.41/13.19  Index Matching       : 0.00
% 22.41/13.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
