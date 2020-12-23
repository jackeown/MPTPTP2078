%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:12 EST 2020

% Result     : Theorem 9.31s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 987 expanded)
%              Number of leaves         :   53 ( 365 expanded)
%              Depth                    :   16
%              Number of atoms          :  305 (3274 expanded)
%              Number of equality atoms :   82 ( 927 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_191,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_165,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_149,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_153,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_163,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_68,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_178,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_187,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_178])).

tff(c_196,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_187])).

tff(c_276,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_288,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_80,c_276])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_184,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_86,c_178])).

tff(c_193,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_184])).

tff(c_287,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_86,c_276])).

tff(c_66,plain,(
    ! [A_54] : k6_relat_1(A_54) = k6_partfun1(A_54) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_24,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_96,plain,(
    ! [A_23] : k1_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_24])).

tff(c_90,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_84,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1711,plain,(
    ! [C_170,D_171,E_168,A_169,F_172,B_173] :
      ( m1_subset_1(k1_partfun1(A_169,B_173,C_170,D_171,E_168,F_172),k1_zfmisc_1(k2_zfmisc_1(A_169,D_171)))
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_170,D_171)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_173)))
      | ~ v1_funct_1(E_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_62,plain,(
    ! [A_47] : m1_subset_1(k6_partfun1(A_47),k1_zfmisc_1(k2_zfmisc_1(A_47,A_47))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_76,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1281,plain,(
    ! [D_142,C_143,A_144,B_145] :
      ( D_142 = C_143
      | ~ r2_relset_1(A_144,B_145,C_143,D_142)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1289,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_76,c_1281])).

tff(c_1304,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1289])).

tff(c_1356,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1304])).

tff(c_1714,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1711,c_1356])).

tff(c_1742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_84,c_80,c_1714])).

tff(c_1743,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1304])).

tff(c_2115,plain,(
    ! [C_200,F_196,E_201,B_198,D_197,A_199] :
      ( k1_partfun1(A_199,B_198,C_200,D_197,E_201,F_196) = k5_relat_1(E_201,F_196)
      | ~ m1_subset_1(F_196,k1_zfmisc_1(k2_zfmisc_1(C_200,D_197)))
      | ~ v1_funct_1(F_196)
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_1(E_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_2121,plain,(
    ! [A_199,B_198,E_201] :
      ( k1_partfun1(A_199,B_198,'#skF_2','#skF_1',E_201,'#skF_4') = k5_relat_1(E_201,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_198)))
      | ~ v1_funct_1(E_201) ) ),
    inference(resolution,[status(thm)],[c_80,c_2115])).

tff(c_2465,plain,(
    ! [A_217,B_218,E_219] :
      ( k1_partfun1(A_217,B_218,'#skF_2','#skF_1',E_219,'#skF_4') = k5_relat_1(E_219,'#skF_4')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_217,B_218)))
      | ~ v1_funct_1(E_219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2121])).

tff(c_2477,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_2465])).

tff(c_2488,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1743,c_2477])).

tff(c_398,plain,(
    ! [A_105,B_106] :
      ( k10_relat_1(A_105,k1_relat_1(B_106)) = k1_relat_1(k5_relat_1(A_105,B_106))
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k10_relat_1(B_11,A_10),k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_416,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_105,B_106)),k1_relat_1(A_105))
      | ~ v1_relat_1(A_105)
      | ~ v1_relat_1(B_106)
      | ~ v1_relat_1(A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_16])).

tff(c_2501,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_416])).

tff(c_2509,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_196,c_193,c_96,c_2501])).

tff(c_198,plain,(
    ! [B_75,A_76] :
      ( r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,(
    ! [B_75,A_76] :
      ( k1_relat_1(B_75) = A_76
      | ~ r1_tarski(A_76,k1_relat_1(B_75))
      | ~ v4_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_198,c_2])).

tff(c_2513,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2509,c_204])).

tff(c_2518,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_287,c_2513])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_442,plain,(
    ! [A_107,B_108,C_109] :
      ( k2_relset_1(A_107,B_108,C_109) = k2_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_448,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_86,c_442])).

tff(c_455,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_448])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_460,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_18])).

tff(c_467,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_460])).

tff(c_734,plain,(
    ! [B_123,A_124] :
      ( k9_relat_1(B_123,k10_relat_1(B_123,A_124)) = A_124
      | ~ r1_tarski(A_124,k2_relat_1(B_123))
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_739,plain,(
    ! [A_124] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_124)) = A_124
      | ~ r1_tarski(A_124,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_734])).

tff(c_761,plain,(
    ! [A_125] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_125)) = A_125
      | ~ r1_tarski(A_125,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_90,c_739])).

tff(c_770,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_467,c_761])).

tff(c_782,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_770])).

tff(c_2522,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2518,c_782])).

tff(c_20,plain,(
    ! [A_13,B_15] :
      ( k10_relat_1(A_13,k1_relat_1(B_15)) = k1_relat_1(k5_relat_1(A_13,B_15))
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_774,plain,(
    ! [B_15] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_15))) = k1_relat_1(B_15)
      | ~ r1_tarski(k1_relat_1(B_15),'#skF_2')
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_761])).

tff(c_784,plain,(
    ! [B_15] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_15))) = k1_relat_1(B_15)
      | ~ r1_tarski(k1_relat_1(B_15),'#skF_2')
      | ~ v1_relat_1(B_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_774])).

tff(c_2498,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_784])).

tff(c_2507,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_96,c_2498])).

tff(c_3207,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2522,c_2507])).

tff(c_3208,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3207])).

tff(c_3211,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3208])).

tff(c_3215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_288,c_3211])).

tff(c_3216,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3207])).

tff(c_28,plain,(
    ! [A_24] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_24)),A_24) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_94,plain,(
    ! [A_24] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_24)),A_24) = A_24
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_28])).

tff(c_3286,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3216,c_94])).

tff(c_3314,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_3286])).

tff(c_74,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_34,plain,(
    ! [A_26] :
      ( v1_relat_1(k2_funct_1(A_26))
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_44,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_relat_1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_91,plain,(
    ! [A_30] :
      ( k5_relat_1(A_30,k2_funct_1(A_30)) = k6_partfun1(k1_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_44])).

tff(c_980,plain,(
    ! [B_134] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_134))) = k1_relat_1(B_134)
      | ~ r1_tarski(k1_relat_1(B_134),'#skF_2')
      | ~ v1_relat_1(B_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_774])).

tff(c_990,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1(k1_relat_1('#skF_3')))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_980])).

tff(c_1005,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_90,c_74,c_782,c_96,c_990])).

tff(c_1012,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1005])).

tff(c_1015,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_1012])).

tff(c_1019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_90,c_1015])).

tff(c_1021,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_313,plain,(
    ! [A_95] :
      ( k2_relat_1(k2_funct_1(A_95)) = k1_relat_1(A_95)
      | ~ v2_funct_1(A_95)
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k6_relat_1(k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_93,plain,(
    ! [A_25] :
      ( k5_relat_1(A_25,k6_partfun1(k2_relat_1(A_25))) = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_30])).

tff(c_3408,plain,(
    ! [A_237] :
      ( k5_relat_1(k2_funct_1(A_237),k6_partfun1(k1_relat_1(A_237))) = k2_funct_1(A_237)
      | ~ v1_relat_1(k2_funct_1(A_237))
      | ~ v2_funct_1(A_237)
      | ~ v1_funct_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_93])).

tff(c_3444,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2518,c_3408])).

tff(c_3480,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_90,c_74,c_1021,c_3444])).

tff(c_42,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_92,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_42])).

tff(c_1034,plain,(
    ! [A_135,B_136,C_137] :
      ( k5_relat_1(k5_relat_1(A_135,B_136),C_137) = k5_relat_1(A_135,k5_relat_1(B_136,C_137))
      | ~ v1_relat_1(C_137)
      | ~ v1_relat_1(B_136)
      | ~ v1_relat_1(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_7492,plain,(
    ! [A_319,C_320] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_319)),C_320) = k5_relat_1(k2_funct_1(A_319),k5_relat_1(A_319,C_320))
      | ~ v1_relat_1(C_320)
      | ~ v1_relat_1(A_319)
      | ~ v1_relat_1(k2_funct_1(A_319))
      | ~ v2_funct_1(A_319)
      | ~ v1_funct_1(A_319)
      | ~ v1_relat_1(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_1034])).

tff(c_7708,plain,(
    ! [C_320] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_320)) = k5_relat_1(k6_partfun1('#skF_2'),C_320)
      | ~ v1_relat_1(C_320)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_7492])).

tff(c_9571,plain,(
    ! [C_359] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_359)) = k5_relat_1(k6_partfun1('#skF_2'),C_359)
      | ~ v1_relat_1(C_359) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_90,c_74,c_1021,c_193,c_7708])).

tff(c_9638,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2488,c_9571])).

tff(c_9685,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_3314,c_3480,c_9638])).

tff(c_9687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_9685])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.31/3.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.60  
% 9.31/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.31/3.61  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.31/3.61  
% 9.31/3.61  %Foreground sorts:
% 9.31/3.61  
% 9.31/3.61  
% 9.31/3.61  %Background operators:
% 9.31/3.61  
% 9.31/3.61  
% 9.31/3.61  %Foreground operators:
% 9.31/3.61  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.31/3.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.31/3.61  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.31/3.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.31/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.31/3.61  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.31/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.31/3.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.31/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.31/3.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.31/3.61  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.31/3.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.31/3.61  tff('#skF_2', type, '#skF_2': $i).
% 9.31/3.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.31/3.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.31/3.61  tff('#skF_3', type, '#skF_3': $i).
% 9.31/3.61  tff('#skF_1', type, '#skF_1': $i).
% 9.31/3.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.31/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.31/3.61  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.31/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.31/3.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 9.31/3.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.31/3.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.31/3.61  tff('#skF_4', type, '#skF_4': $i).
% 9.31/3.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.31/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.31/3.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.31/3.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.31/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.31/3.61  
% 9.49/3.63  tff(f_191, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 9.49/3.63  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.49/3.63  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.49/3.63  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.49/3.63  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.49/3.63  tff(f_165, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.49/3.63  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.49/3.63  tff(f_149, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.49/3.63  tff(f_153, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.49/3.63  tff(f_137, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.49/3.63  tff(f_163, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.49/3.63  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 9.49/3.63  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 9.49/3.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.49/3.63  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.49/3.63  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 9.49/3.63  tff(f_99, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 9.49/3.63  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 9.49/3.63  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 9.49/3.63  tff(f_119, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 9.49/3.63  tff(f_109, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 9.49/3.63  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 9.49/3.63  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 9.49/3.63  tff(c_68, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.49/3.63  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_178, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.49/3.63  tff(c_187, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_80, c_178])).
% 9.49/3.63  tff(c_196, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_187])).
% 9.49/3.63  tff(c_276, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.49/3.63  tff(c_288, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_80, c_276])).
% 9.49/3.63  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.49/3.63  tff(c_86, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_184, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_86, c_178])).
% 9.49/3.63  tff(c_193, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_184])).
% 9.49/3.63  tff(c_287, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_86, c_276])).
% 9.49/3.63  tff(c_66, plain, (![A_54]: (k6_relat_1(A_54)=k6_partfun1(A_54))), inference(cnfTransformation, [status(thm)], [f_165])).
% 9.49/3.63  tff(c_24, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.49/3.63  tff(c_96, plain, (![A_23]: (k1_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_24])).
% 9.49/3.63  tff(c_90, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_84, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_1711, plain, (![C_170, D_171, E_168, A_169, F_172, B_173]: (m1_subset_1(k1_partfun1(A_169, B_173, C_170, D_171, E_168, F_172), k1_zfmisc_1(k2_zfmisc_1(A_169, D_171))) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_170, D_171))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_173))) | ~v1_funct_1(E_168))), inference(cnfTransformation, [status(thm)], [f_149])).
% 9.49/3.63  tff(c_62, plain, (![A_47]: (m1_subset_1(k6_partfun1(A_47), k1_zfmisc_1(k2_zfmisc_1(A_47, A_47))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 9.49/3.63  tff(c_76, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_1281, plain, (![D_142, C_143, A_144, B_145]: (D_142=C_143 | ~r2_relset_1(A_144, B_145, C_143, D_142) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 9.49/3.63  tff(c_1289, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_76, c_1281])).
% 9.49/3.63  tff(c_1304, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1289])).
% 9.49/3.63  tff(c_1356, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1304])).
% 9.49/3.63  tff(c_1714, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1711, c_1356])).
% 9.49/3.63  tff(c_1742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_84, c_80, c_1714])).
% 9.49/3.63  tff(c_1743, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1304])).
% 9.49/3.63  tff(c_2115, plain, (![C_200, F_196, E_201, B_198, D_197, A_199]: (k1_partfun1(A_199, B_198, C_200, D_197, E_201, F_196)=k5_relat_1(E_201, F_196) | ~m1_subset_1(F_196, k1_zfmisc_1(k2_zfmisc_1(C_200, D_197))) | ~v1_funct_1(F_196) | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_1(E_201))), inference(cnfTransformation, [status(thm)], [f_163])).
% 9.49/3.63  tff(c_2121, plain, (![A_199, B_198, E_201]: (k1_partfun1(A_199, B_198, '#skF_2', '#skF_1', E_201, '#skF_4')=k5_relat_1(E_201, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_198))) | ~v1_funct_1(E_201))), inference(resolution, [status(thm)], [c_80, c_2115])).
% 9.49/3.63  tff(c_2465, plain, (![A_217, B_218, E_219]: (k1_partfun1(A_217, B_218, '#skF_2', '#skF_1', E_219, '#skF_4')=k5_relat_1(E_219, '#skF_4') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_217, B_218))) | ~v1_funct_1(E_219))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2121])).
% 9.49/3.63  tff(c_2477, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_2465])).
% 9.49/3.63  tff(c_2488, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1743, c_2477])).
% 9.49/3.63  tff(c_398, plain, (![A_105, B_106]: (k10_relat_1(A_105, k1_relat_1(B_106))=k1_relat_1(k5_relat_1(A_105, B_106)) | ~v1_relat_1(B_106) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.49/3.63  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k10_relat_1(B_11, A_10), k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.49/3.63  tff(c_416, plain, (![A_105, B_106]: (r1_tarski(k1_relat_1(k5_relat_1(A_105, B_106)), k1_relat_1(A_105)) | ~v1_relat_1(A_105) | ~v1_relat_1(B_106) | ~v1_relat_1(A_105))), inference(superposition, [status(thm), theory('equality')], [c_398, c_16])).
% 9.49/3.63  tff(c_2501, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2488, c_416])).
% 9.49/3.63  tff(c_2509, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_196, c_193, c_96, c_2501])).
% 9.49/3.63  tff(c_198, plain, (![B_75, A_76]: (r1_tarski(k1_relat_1(B_75), A_76) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.49/3.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.63  tff(c_204, plain, (![B_75, A_76]: (k1_relat_1(B_75)=A_76 | ~r1_tarski(A_76, k1_relat_1(B_75)) | ~v4_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_198, c_2])).
% 9.49/3.63  tff(c_2513, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2509, c_204])).
% 9.49/3.63  tff(c_2518, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_287, c_2513])).
% 9.49/3.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.63  tff(c_78, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_442, plain, (![A_107, B_108, C_109]: (k2_relset_1(A_107, B_108, C_109)=k2_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 9.49/3.63  tff(c_448, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_86, c_442])).
% 9.49/3.63  tff(c_455, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_448])).
% 9.49/3.63  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.49/3.63  tff(c_460, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_455, c_18])).
% 9.49/3.63  tff(c_467, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_460])).
% 9.49/3.63  tff(c_734, plain, (![B_123, A_124]: (k9_relat_1(B_123, k10_relat_1(B_123, A_124))=A_124 | ~r1_tarski(A_124, k2_relat_1(B_123)) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.49/3.63  tff(c_739, plain, (![A_124]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_124))=A_124 | ~r1_tarski(A_124, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_455, c_734])).
% 9.49/3.63  tff(c_761, plain, (![A_125]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_125))=A_125 | ~r1_tarski(A_125, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_90, c_739])).
% 9.49/3.63  tff(c_770, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_467, c_761])).
% 9.49/3.63  tff(c_782, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_770])).
% 9.49/3.63  tff(c_2522, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2518, c_782])).
% 9.49/3.63  tff(c_20, plain, (![A_13, B_15]: (k10_relat_1(A_13, k1_relat_1(B_15))=k1_relat_1(k5_relat_1(A_13, B_15)) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.49/3.63  tff(c_774, plain, (![B_15]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_15)))=k1_relat_1(B_15) | ~r1_tarski(k1_relat_1(B_15), '#skF_2') | ~v1_relat_1(B_15) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_761])).
% 9.49/3.63  tff(c_784, plain, (![B_15]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_15)))=k1_relat_1(B_15) | ~r1_tarski(k1_relat_1(B_15), '#skF_2') | ~v1_relat_1(B_15))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_774])).
% 9.49/3.63  tff(c_2498, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2488, c_784])).
% 9.49/3.63  tff(c_2507, plain, (k9_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_96, c_2498])).
% 9.49/3.63  tff(c_3207, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2522, c_2507])).
% 9.49/3.63  tff(c_3208, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3207])).
% 9.49/3.63  tff(c_3211, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3208])).
% 9.49/3.63  tff(c_3215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_196, c_288, c_3211])).
% 9.49/3.63  tff(c_3216, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_3207])).
% 9.49/3.63  tff(c_28, plain, (![A_24]: (k5_relat_1(k6_relat_1(k1_relat_1(A_24)), A_24)=A_24 | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.49/3.63  tff(c_94, plain, (![A_24]: (k5_relat_1(k6_partfun1(k1_relat_1(A_24)), A_24)=A_24 | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_28])).
% 9.49/3.63  tff(c_3286, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3216, c_94])).
% 9.49/3.63  tff(c_3314, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_3286])).
% 9.49/3.63  tff(c_74, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_191])).
% 9.49/3.63  tff(c_34, plain, (![A_26]: (v1_relat_1(k2_funct_1(A_26)) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.49/3.63  tff(c_44, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_relat_1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.49/3.63  tff(c_91, plain, (![A_30]: (k5_relat_1(A_30, k2_funct_1(A_30))=k6_partfun1(k1_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_44])).
% 9.49/3.63  tff(c_980, plain, (![B_134]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_134)))=k1_relat_1(B_134) | ~r1_tarski(k1_relat_1(B_134), '#skF_2') | ~v1_relat_1(B_134))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_774])).
% 9.49/3.63  tff(c_990, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_91, c_980])).
% 9.49/3.63  tff(c_1005, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_90, c_74, c_782, c_96, c_990])).
% 9.49/3.63  tff(c_1012, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1005])).
% 9.49/3.63  tff(c_1015, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_1012])).
% 9.49/3.63  tff(c_1019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_90, c_1015])).
% 9.49/3.63  tff(c_1021, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1005])).
% 9.49/3.63  tff(c_313, plain, (![A_95]: (k2_relat_1(k2_funct_1(A_95))=k1_relat_1(A_95) | ~v2_funct_1(A_95) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.49/3.63  tff(c_30, plain, (![A_25]: (k5_relat_1(A_25, k6_relat_1(k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.49/3.63  tff(c_93, plain, (![A_25]: (k5_relat_1(A_25, k6_partfun1(k2_relat_1(A_25)))=A_25 | ~v1_relat_1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_30])).
% 9.49/3.63  tff(c_3408, plain, (![A_237]: (k5_relat_1(k2_funct_1(A_237), k6_partfun1(k1_relat_1(A_237)))=k2_funct_1(A_237) | ~v1_relat_1(k2_funct_1(A_237)) | ~v2_funct_1(A_237) | ~v1_funct_1(A_237) | ~v1_relat_1(A_237))), inference(superposition, [status(thm), theory('equality')], [c_313, c_93])).
% 9.49/3.63  tff(c_3444, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2518, c_3408])).
% 9.49/3.63  tff(c_3480, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_90, c_74, c_1021, c_3444])).
% 9.49/3.63  tff(c_42, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.49/3.63  tff(c_92, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_42])).
% 9.49/3.63  tff(c_1034, plain, (![A_135, B_136, C_137]: (k5_relat_1(k5_relat_1(A_135, B_136), C_137)=k5_relat_1(A_135, k5_relat_1(B_136, C_137)) | ~v1_relat_1(C_137) | ~v1_relat_1(B_136) | ~v1_relat_1(A_135))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.49/3.63  tff(c_7492, plain, (![A_319, C_320]: (k5_relat_1(k6_partfun1(k2_relat_1(A_319)), C_320)=k5_relat_1(k2_funct_1(A_319), k5_relat_1(A_319, C_320)) | ~v1_relat_1(C_320) | ~v1_relat_1(A_319) | ~v1_relat_1(k2_funct_1(A_319)) | ~v2_funct_1(A_319) | ~v1_funct_1(A_319) | ~v1_relat_1(A_319))), inference(superposition, [status(thm), theory('equality')], [c_92, c_1034])).
% 9.49/3.63  tff(c_7708, plain, (![C_320]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_320))=k5_relat_1(k6_partfun1('#skF_2'), C_320) | ~v1_relat_1(C_320) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_455, c_7492])).
% 9.49/3.63  tff(c_9571, plain, (![C_359]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_359))=k5_relat_1(k6_partfun1('#skF_2'), C_359) | ~v1_relat_1(C_359))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_90, c_74, c_1021, c_193, c_7708])).
% 9.49/3.63  tff(c_9638, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2488, c_9571])).
% 9.49/3.63  tff(c_9685, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_3314, c_3480, c_9638])).
% 9.49/3.63  tff(c_9687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_9685])).
% 9.49/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.63  
% 9.49/3.63  Inference rules
% 9.49/3.63  ----------------------
% 9.49/3.63  #Ref     : 0
% 9.49/3.63  #Sup     : 2076
% 9.49/3.63  #Fact    : 0
% 9.49/3.63  #Define  : 0
% 9.49/3.63  #Split   : 11
% 9.49/3.63  #Chain   : 0
% 9.49/3.63  #Close   : 0
% 9.49/3.63  
% 9.49/3.63  Ordering : KBO
% 9.49/3.63  
% 9.49/3.63  Simplification rules
% 9.49/3.63  ----------------------
% 9.49/3.63  #Subsume      : 107
% 9.49/3.63  #Demod        : 3362
% 9.49/3.63  #Tautology    : 796
% 9.49/3.63  #SimpNegUnit  : 1
% 9.49/3.63  #BackRed      : 17
% 9.49/3.63  
% 9.49/3.63  #Partial instantiations: 0
% 9.49/3.63  #Strategies tried      : 1
% 9.49/3.63  
% 9.49/3.63  Timing (in seconds)
% 9.49/3.63  ----------------------
% 9.49/3.63  Preprocessing        : 0.37
% 9.49/3.63  Parsing              : 0.20
% 9.49/3.63  CNF conversion       : 0.03
% 9.49/3.63  Main loop            : 2.47
% 9.49/3.63  Inferencing          : 0.68
% 9.49/3.63  Reduction            : 1.17
% 9.49/3.63  Demodulation         : 0.97
% 9.49/3.63  BG Simplification    : 0.07
% 9.49/3.63  Subsumption          : 0.42
% 9.49/3.63  Abstraction          : 0.09
% 9.49/3.63  MUC search           : 0.00
% 9.49/3.63  Cooper               : 0.00
% 9.49/3.63  Total                : 2.89
% 9.49/3.63  Index Insertion      : 0.00
% 9.49/3.63  Index Deletion       : 0.00
% 9.49/3.63  Index Matching       : 0.00
% 9.49/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
