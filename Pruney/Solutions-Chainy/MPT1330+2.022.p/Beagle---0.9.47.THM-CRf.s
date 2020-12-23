%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:12 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 492 expanded)
%              Number of leaves         :   50 ( 188 expanded)
%              Depth                    :   13
%              Number of atoms          :  186 (1191 expanded)
%              Number of equality atoms :   72 ( 461 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( l1_struct_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_struct_0(B) = k1_xboole_0
                   => k2_struct_0(A) = k1_xboole_0 )
                 => k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,k2_struct_0(B)) = k2_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_125,axiom,(
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

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_92,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_100,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_92])).

tff(c_72,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_99,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_92])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_145,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_99,c_66])).

tff(c_193,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_196,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_145,c_193])).

tff(c_199,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_196])).

tff(c_36,plain,(
    ! [A_25] :
      ( k10_relat_1(A_25,k2_relat_1(A_25)) = k1_relat_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_211,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_215,plain,(
    v5_relat_1('#skF_6',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_145,c_211])).

tff(c_201,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k2_relat_1(B_72),A_73)
      | ~ v5_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_685,plain,(
    ! [B_159,A_160] :
      ( k3_xboole_0(k2_relat_1(B_159),A_160) = k2_relat_1(B_159)
      | ~ v5_relat_1(B_159,A_160)
      | ~ v1_relat_1(B_159) ) ),
    inference(resolution,[status(thm)],[c_201,c_8])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( k10_relat_1(B_24,k3_xboole_0(k2_relat_1(B_24),A_23)) = k10_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1109,plain,(
    ! [B_218,A_219] :
      ( k10_relat_1(B_218,k2_relat_1(B_218)) = k10_relat_1(B_218,A_219)
      | ~ v1_relat_1(B_218)
      | ~ v5_relat_1(B_218,A_219)
      | ~ v1_relat_1(B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_34])).

tff(c_1111,plain,
    ( k10_relat_1('#skF_6',k2_struct_0('#skF_5')) = k10_relat_1('#skF_6',k2_relat_1('#skF_6'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_215,c_1109])).

tff(c_1114,plain,(
    k10_relat_1('#skF_6',k2_struct_0('#skF_5')) = k10_relat_1('#skF_6',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1111])).

tff(c_206,plain,(
    ! [C_74,A_75,B_76] :
      ( v4_relat_1(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_210,plain,(
    v4_relat_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_145,c_206])).

tff(c_382,plain,(
    ! [B_111,A_112] :
      ( k1_relat_1(B_111) = A_112
      | ~ v1_partfun1(B_111,A_112)
      | ~ v4_relat_1(B_111,A_112)
      | ~ v1_relat_1(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_385,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_210,c_382])).

tff(c_388,plain,
    ( k2_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_385])).

tff(c_389,plain,(
    ~ v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_388])).

tff(c_64,plain,
    ( k2_struct_0('#skF_4') = k1_xboole_0
    | k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_116,plain,(
    k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_101,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_68])).

tff(c_146,plain,(
    v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_101])).

tff(c_630,plain,(
    ! [B_154,C_155,A_156] :
      ( k1_xboole_0 = B_154
      | v1_partfun1(C_155,A_156)
      | ~ v1_funct_2(C_155,A_156,B_154)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_156,B_154)))
      | ~ v1_funct_1(C_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_633,plain,
    ( k2_struct_0('#skF_5') = k1_xboole_0
    | v1_partfun1('#skF_6',k2_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',k2_struct_0('#skF_4'),k2_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_145,c_630])).

tff(c_636,plain,
    ( k2_struct_0('#skF_5') = k1_xboole_0
    | v1_partfun1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_146,c_633])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_116,c_636])).

tff(c_639,plain,(
    k2_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_388])).

tff(c_644,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_145])).

tff(c_817,plain,(
    ! [A_176,B_177,C_178,D_179] :
      ( k8_relset_1(A_176,B_177,C_178,D_179) = k10_relat_1(C_178,D_179)
      | ~ m1_subset_1(C_178,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_820,plain,(
    ! [D_179] : k8_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6',D_179) = k10_relat_1('#skF_6',D_179) ),
    inference(resolution,[status(thm)],[c_644,c_817])).

tff(c_62,plain,(
    k8_relset_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) != k2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_200,plain,(
    k8_relset_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) != k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_99,c_62])).

tff(c_642,plain,(
    k8_relset_1(k1_relat_1('#skF_6'),k2_struct_0('#skF_5'),'#skF_6',k2_struct_0('#skF_5')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_639,c_639,c_200])).

tff(c_833,plain,(
    k10_relat_1('#skF_6',k2_struct_0('#skF_5')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_642])).

tff(c_1116,plain,(
    k10_relat_1('#skF_6',k2_relat_1('#skF_6')) != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1114,c_833])).

tff(c_1123,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1116])).

tff(c_1127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_1123])).

tff(c_1128,plain,(
    k2_struct_0('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1130,plain,(
    u1_struct_0('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1128,c_100])).

tff(c_1129,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1135,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_66])).

tff(c_1136,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1135])).

tff(c_1202,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_1136])).

tff(c_1218,plain,(
    ! [B_234,A_235] :
      ( v1_relat_1(B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(A_235))
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1221,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1202,c_1218])).

tff(c_1224,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1221])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_51,B_52] : k2_xboole_0(k1_tarski(A_51),B_52) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,(
    ! [A_51] : k1_tarski(A_51) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_86])).

tff(c_1150,plain,(
    ! [A_222] :
      ( r2_hidden('#skF_3'(A_222),A_222)
      | k1_xboole_0 = A_222 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1154,plain,(
    ! [A_9] :
      ( '#skF_3'(k1_tarski(A_9)) = A_9
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1150,c_12])).

tff(c_1157,plain,(
    ! [A_9] : '#skF_3'(k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1154])).

tff(c_1172,plain,(
    ! [A_224] :
      ( r1_xboole_0('#skF_3'(A_224),A_224)
      | k1_xboole_0 = A_224 ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1175,plain,(
    ! [A_9] :
      ( r1_xboole_0(A_9,k1_tarski(A_9))
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_1172])).

tff(c_1176,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_tarski(A_9)) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1175])).

tff(c_1182,plain,(
    ! [A_230,B_231] :
      ( k3_xboole_0(A_230,B_231) = k1_xboole_0
      | ~ r1_xboole_0(A_230,B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1193,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_tarski(A_9)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1176,c_1182])).

tff(c_1369,plain,(
    ! [B_272,A_273] :
      ( k10_relat_1(B_272,k3_xboole_0(k2_relat_1(B_272),A_273)) = k10_relat_1(B_272,A_273)
      | ~ v1_relat_1(B_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1387,plain,(
    ! [B_276] :
      ( k10_relat_1(B_276,k1_tarski(k2_relat_1(B_276))) = k10_relat_1(B_276,k1_xboole_0)
      | ~ v1_relat_1(B_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1193,c_1369])).

tff(c_1315,plain,(
    ! [B_257,A_258] :
      ( k10_relat_1(B_257,A_258) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_257),A_258)
      | ~ v1_relat_1(B_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1330,plain,(
    ! [B_257] :
      ( k10_relat_1(B_257,k1_tarski(k2_relat_1(B_257))) = k1_xboole_0
      | ~ v1_relat_1(B_257) ) ),
    inference(resolution,[status(thm)],[c_1176,c_1315])).

tff(c_1402,plain,(
    ! [B_277] :
      ( k10_relat_1(B_277,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_277)
      | ~ v1_relat_1(B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1387,c_1330])).

tff(c_1404,plain,
    ( k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_1224,c_1402])).

tff(c_1409,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_1404])).

tff(c_1551,plain,(
    ! [A_295,B_296,C_297,D_298] :
      ( k8_relset_1(A_295,B_296,C_297,D_298) = k10_relat_1(C_297,D_298)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1554,plain,(
    ! [D_298] : k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6',D_298) = k10_relat_1('#skF_6',D_298) ),
    inference(resolution,[status(thm)],[c_1202,c_1551])).

tff(c_1137,plain,(
    u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_99])).

tff(c_1180,plain,(
    k8_relset_1(k1_xboole_0,k1_xboole_0,'#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1137,c_1130,c_1129,c_1128,c_62])).

tff(c_1555,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1554,c_1180])).

tff(c_1558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1409,c_1555])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:49:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k8_relset_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k10_relat_1 > #nlpp > u1_struct_0 > k2_struct_0 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 3.48/1.60  
% 3.48/1.60  %Foreground sorts:
% 3.48/1.60  
% 3.48/1.60  
% 3.48/1.60  %Background operators:
% 3.48/1.60  
% 3.48/1.60  
% 3.48/1.60  %Foreground operators:
% 3.48/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.48/1.60  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.48/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.48/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.48/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.48/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.48/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.48/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.48/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.48/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.48/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.48/1.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.48/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.48/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.48/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.48/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.48/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.48/1.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.48/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.60  
% 3.48/1.62  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.48/1.62  tff(f_148, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_struct_0(B) = k1_xboole_0) => (k2_struct_0(A) = k1_xboole_0)) => (k8_relset_1(u1_struct_0(A), u1_struct_0(B), C, k2_struct_0(B)) = k2_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tops_2)).
% 3.48/1.62  tff(f_129, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.48/1.62  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.48/1.62  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.48/1.62  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.48/1.62  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.48/1.62  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.48/1.62  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_relat_1)).
% 3.48/1.62  tff(f_108, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 3.48/1.62  tff(f_125, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t132_funct_2)).
% 3.48/1.62  tff(f_90, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.48/1.62  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.48/1.62  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.48/1.62  tff(f_100, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.48/1.62  tff(f_48, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.48/1.62  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.48/1.62  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.48/1.62  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.62  tff(c_74, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_92, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.48/1.62  tff(c_100, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_74, c_92])).
% 3.48/1.62  tff(c_72, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_99, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_92])).
% 3.48/1.62  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_145, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_99, c_66])).
% 3.48/1.62  tff(c_193, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.62  tff(c_196, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_145, c_193])).
% 3.48/1.62  tff(c_199, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_196])).
% 3.48/1.62  tff(c_36, plain, (![A_25]: (k10_relat_1(A_25, k2_relat_1(A_25))=k1_relat_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.48/1.62  tff(c_211, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.48/1.62  tff(c_215, plain, (v5_relat_1('#skF_6', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_145, c_211])).
% 3.48/1.62  tff(c_201, plain, (![B_72, A_73]: (r1_tarski(k2_relat_1(B_72), A_73) | ~v5_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.48/1.62  tff(c_8, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.62  tff(c_685, plain, (![B_159, A_160]: (k3_xboole_0(k2_relat_1(B_159), A_160)=k2_relat_1(B_159) | ~v5_relat_1(B_159, A_160) | ~v1_relat_1(B_159))), inference(resolution, [status(thm)], [c_201, c_8])).
% 3.48/1.62  tff(c_34, plain, (![B_24, A_23]: (k10_relat_1(B_24, k3_xboole_0(k2_relat_1(B_24), A_23))=k10_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.62  tff(c_1109, plain, (![B_218, A_219]: (k10_relat_1(B_218, k2_relat_1(B_218))=k10_relat_1(B_218, A_219) | ~v1_relat_1(B_218) | ~v5_relat_1(B_218, A_219) | ~v1_relat_1(B_218))), inference(superposition, [status(thm), theory('equality')], [c_685, c_34])).
% 3.48/1.62  tff(c_1111, plain, (k10_relat_1('#skF_6', k2_struct_0('#skF_5'))=k10_relat_1('#skF_6', k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_215, c_1109])).
% 3.48/1.62  tff(c_1114, plain, (k10_relat_1('#skF_6', k2_struct_0('#skF_5'))=k10_relat_1('#skF_6', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_1111])).
% 3.48/1.62  tff(c_206, plain, (![C_74, A_75, B_76]: (v4_relat_1(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.48/1.62  tff(c_210, plain, (v4_relat_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_145, c_206])).
% 3.48/1.62  tff(c_382, plain, (![B_111, A_112]: (k1_relat_1(B_111)=A_112 | ~v1_partfun1(B_111, A_112) | ~v4_relat_1(B_111, A_112) | ~v1_relat_1(B_111))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.48/1.62  tff(c_385, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_210, c_382])).
% 3.48/1.62  tff(c_388, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_199, c_385])).
% 3.48/1.62  tff(c_389, plain, (~v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_388])).
% 3.48/1.62  tff(c_64, plain, (k2_struct_0('#skF_4')=k1_xboole_0 | k2_struct_0('#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_116, plain, (k2_struct_0('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_64])).
% 3.48/1.62  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_68, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_101, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_68])).
% 3.48/1.62  tff(c_146, plain, (v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_101])).
% 3.48/1.62  tff(c_630, plain, (![B_154, C_155, A_156]: (k1_xboole_0=B_154 | v1_partfun1(C_155, A_156) | ~v1_funct_2(C_155, A_156, B_154) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_156, B_154))) | ~v1_funct_1(C_155))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.48/1.62  tff(c_633, plain, (k2_struct_0('#skF_5')=k1_xboole_0 | v1_partfun1('#skF_6', k2_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', k2_struct_0('#skF_4'), k2_struct_0('#skF_5')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_145, c_630])).
% 3.48/1.62  tff(c_636, plain, (k2_struct_0('#skF_5')=k1_xboole_0 | v1_partfun1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_146, c_633])).
% 3.48/1.62  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_116, c_636])).
% 3.48/1.62  tff(c_639, plain, (k2_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_388])).
% 3.48/1.62  tff(c_644, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_639, c_145])).
% 3.48/1.62  tff(c_817, plain, (![A_176, B_177, C_178, D_179]: (k8_relset_1(A_176, B_177, C_178, D_179)=k10_relat_1(C_178, D_179) | ~m1_subset_1(C_178, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.48/1.62  tff(c_820, plain, (![D_179]: (k8_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6', D_179)=k10_relat_1('#skF_6', D_179))), inference(resolution, [status(thm)], [c_644, c_817])).
% 3.48/1.62  tff(c_62, plain, (k8_relset_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.48/1.62  tff(c_200, plain, (k8_relset_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))!=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_99, c_62])).
% 3.48/1.62  tff(c_642, plain, (k8_relset_1(k1_relat_1('#skF_6'), k2_struct_0('#skF_5'), '#skF_6', k2_struct_0('#skF_5'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_639, c_639, c_200])).
% 3.48/1.62  tff(c_833, plain, (k10_relat_1('#skF_6', k2_struct_0('#skF_5'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_642])).
% 3.48/1.62  tff(c_1116, plain, (k10_relat_1('#skF_6', k2_relat_1('#skF_6'))!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1114, c_833])).
% 3.48/1.62  tff(c_1123, plain, (~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1116])).
% 3.48/1.62  tff(c_1127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_1123])).
% 3.48/1.62  tff(c_1128, plain, (k2_struct_0('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 3.48/1.62  tff(c_1130, plain, (u1_struct_0('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1128, c_100])).
% 3.48/1.62  tff(c_1129, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_64])).
% 3.48/1.62  tff(c_1135, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_66])).
% 3.48/1.62  tff(c_1136, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1135])).
% 3.48/1.62  tff(c_1202, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_1136])).
% 3.48/1.62  tff(c_1218, plain, (![B_234, A_235]: (v1_relat_1(B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(A_235)) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.62  tff(c_1221, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_1202, c_1218])).
% 3.48/1.62  tff(c_1224, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1221])).
% 3.48/1.62  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.62  tff(c_86, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.62  tff(c_90, plain, (![A_51]: (k1_tarski(A_51)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_86])).
% 3.48/1.62  tff(c_1150, plain, (![A_222]: (r2_hidden('#skF_3'(A_222), A_222) | k1_xboole_0=A_222)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.48/1.62  tff(c_12, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.48/1.62  tff(c_1154, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9 | k1_tarski(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1150, c_12])).
% 3.48/1.62  tff(c_1157, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_90, c_1154])).
% 3.48/1.62  tff(c_1172, plain, (![A_224]: (r1_xboole_0('#skF_3'(A_224), A_224) | k1_xboole_0=A_224)), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.48/1.62  tff(c_1175, plain, (![A_9]: (r1_xboole_0(A_9, k1_tarski(A_9)) | k1_tarski(A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1157, c_1172])).
% 3.48/1.62  tff(c_1176, plain, (![A_9]: (r1_xboole_0(A_9, k1_tarski(A_9)))), inference(negUnitSimplification, [status(thm)], [c_90, c_1175])).
% 3.48/1.62  tff(c_1182, plain, (![A_230, B_231]: (k3_xboole_0(A_230, B_231)=k1_xboole_0 | ~r1_xboole_0(A_230, B_231))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.62  tff(c_1193, plain, (![A_9]: (k3_xboole_0(A_9, k1_tarski(A_9))=k1_xboole_0)), inference(resolution, [status(thm)], [c_1176, c_1182])).
% 3.48/1.62  tff(c_1369, plain, (![B_272, A_273]: (k10_relat_1(B_272, k3_xboole_0(k2_relat_1(B_272), A_273))=k10_relat_1(B_272, A_273) | ~v1_relat_1(B_272))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.62  tff(c_1387, plain, (![B_276]: (k10_relat_1(B_276, k1_tarski(k2_relat_1(B_276)))=k10_relat_1(B_276, k1_xboole_0) | ~v1_relat_1(B_276))), inference(superposition, [status(thm), theory('equality')], [c_1193, c_1369])).
% 3.48/1.62  tff(c_1315, plain, (![B_257, A_258]: (k10_relat_1(B_257, A_258)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_257), A_258) | ~v1_relat_1(B_257))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.48/1.62  tff(c_1330, plain, (![B_257]: (k10_relat_1(B_257, k1_tarski(k2_relat_1(B_257)))=k1_xboole_0 | ~v1_relat_1(B_257))), inference(resolution, [status(thm)], [c_1176, c_1315])).
% 3.48/1.62  tff(c_1402, plain, (![B_277]: (k10_relat_1(B_277, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_277) | ~v1_relat_1(B_277))), inference(superposition, [status(thm), theory('equality')], [c_1387, c_1330])).
% 3.48/1.62  tff(c_1404, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_1224, c_1402])).
% 3.48/1.62  tff(c_1409, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1224, c_1404])).
% 3.48/1.62  tff(c_1551, plain, (![A_295, B_296, C_297, D_298]: (k8_relset_1(A_295, B_296, C_297, D_298)=k10_relat_1(C_297, D_298) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.48/1.62  tff(c_1554, plain, (![D_298]: (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6', D_298)=k10_relat_1('#skF_6', D_298))), inference(resolution, [status(thm)], [c_1202, c_1551])).
% 3.48/1.62  tff(c_1137, plain, (u1_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_99])).
% 3.48/1.62  tff(c_1180, plain, (k8_relset_1(k1_xboole_0, k1_xboole_0, '#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1137, c_1130, c_1129, c_1128, c_62])).
% 3.48/1.62  tff(c_1555, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1554, c_1180])).
% 3.48/1.62  tff(c_1558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1409, c_1555])).
% 3.48/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.62  
% 3.48/1.62  Inference rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Ref     : 0
% 3.48/1.62  #Sup     : 328
% 3.48/1.62  #Fact    : 0
% 3.48/1.62  #Define  : 0
% 3.48/1.62  #Split   : 4
% 3.48/1.62  #Chain   : 0
% 3.48/1.62  #Close   : 0
% 3.48/1.62  
% 3.48/1.62  Ordering : KBO
% 3.48/1.62  
% 3.48/1.62  Simplification rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Subsume      : 37
% 3.48/1.62  #Demod        : 73
% 3.48/1.62  #Tautology    : 163
% 3.48/1.62  #SimpNegUnit  : 18
% 3.48/1.62  #BackRed      : 13
% 3.48/1.62  
% 3.48/1.62  #Partial instantiations: 0
% 3.48/1.62  #Strategies tried      : 1
% 3.48/1.62  
% 3.48/1.62  Timing (in seconds)
% 3.48/1.62  ----------------------
% 3.48/1.62  Preprocessing        : 0.36
% 3.48/1.62  Parsing              : 0.19
% 3.48/1.62  CNF conversion       : 0.03
% 3.48/1.62  Main loop            : 0.48
% 3.48/1.62  Inferencing          : 0.19
% 3.48/1.62  Reduction            : 0.14
% 3.48/1.62  Demodulation         : 0.09
% 3.48/1.62  BG Simplification    : 0.03
% 3.48/1.62  Subsumption          : 0.08
% 3.48/1.62  Abstraction          : 0.02
% 3.48/1.62  MUC search           : 0.00
% 3.48/1.62  Cooper               : 0.00
% 3.48/1.62  Total                : 0.88
% 3.48/1.62  Index Insertion      : 0.00
% 3.48/1.62  Index Deletion       : 0.00
% 3.48/1.62  Index Matching       : 0.00
% 3.48/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
