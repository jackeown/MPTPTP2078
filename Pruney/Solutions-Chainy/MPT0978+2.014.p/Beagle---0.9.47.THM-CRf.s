%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 167 expanded)
%              Number of leaves         :   39 (  74 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 436 expanded)
%              Number of equality atoms :   37 (  86 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_99,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_52,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_234,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_252,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_234])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_266,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_42])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_126,plain,(
    ! [B_60,A_61] :
      ( v1_relat_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_61))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_135,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_126])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_135])).

tff(c_138,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_126])).

tff(c_148,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_138])).

tff(c_297,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1(k2_relset_1(A_87,B_88,C_89),k1_zfmisc_1(B_88))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_313,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_297])).

tff(c_325,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_313])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_357,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_40,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_50,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_465,plain,(
    ! [C_105,B_102,F_104,E_106,D_101,A_103] :
      ( k4_relset_1(A_103,B_102,C_105,D_101,E_106,F_104) = k5_relat_1(E_106,F_104)
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(C_105,D_101)))
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_647,plain,(
    ! [A_124,B_125,E_126] :
      ( k4_relset_1(A_124,B_125,'#skF_1','#skF_2',E_126,'#skF_3') = k5_relat_1(E_126,'#skF_3')
      | ~ m1_subset_1(E_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(resolution,[status(thm)],[c_52,c_465])).

tff(c_686,plain,(
    k4_relset_1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_647])).

tff(c_24,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( m1_subset_1(k4_relset_1(A_17,B_18,C_19,D_20,E_21,F_22),k1_zfmisc_1(k2_zfmisc_1(A_17,D_20)))
      | ~ m1_subset_1(F_22,k1_zfmisc_1(k2_zfmisc_1(C_19,D_20)))
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_804,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_686,c_24])).

tff(c_808,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52,c_804])).

tff(c_56,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_749,plain,(
    ! [D_130,F_129,C_132,A_127,E_131,B_128] :
      ( k1_partfun1(A_127,B_128,C_132,D_130,E_131,F_129) = k5_relat_1(E_131,F_129)
      | ~ m1_subset_1(F_129,k1_zfmisc_1(k2_zfmisc_1(C_132,D_130)))
      | ~ v1_funct_1(F_129)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_773,plain,(
    ! [A_127,B_128,E_131] :
      ( k1_partfun1(A_127,B_128,'#skF_1','#skF_2',E_131,'#skF_3') = k5_relat_1(E_131,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_52,c_749])).

tff(c_1580,plain,(
    ! [A_171,B_172,E_173] :
      ( k1_partfun1(A_171,B_172,'#skF_1','#skF_2',E_173,'#skF_3') = k5_relat_1(E_173,'#skF_3')
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_1(E_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_773])).

tff(c_1629,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1580])).

tff(c_1649,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1629])).

tff(c_36,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_44,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_384,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_394,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_44,c_384])).

tff(c_413,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_394])).

tff(c_414,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_1653,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1649,c_414])).

tff(c_1657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_1653])).

tff(c_1658,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_2054,plain,(
    ! [E_216,F_214,D_215,C_217,B_213,A_212] :
      ( k1_partfun1(A_212,B_213,C_217,D_215,E_216,F_214) = k5_relat_1(E_216,F_214)
      | ~ m1_subset_1(F_214,k1_zfmisc_1(k2_zfmisc_1(C_217,D_215)))
      | ~ v1_funct_1(F_214)
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_1(E_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2078,plain,(
    ! [A_212,B_213,E_216] :
      ( k1_partfun1(A_212,B_213,'#skF_1','#skF_2',E_216,'#skF_3') = k5_relat_1(E_216,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_216,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213)))
      | ~ v1_funct_1(E_216) ) ),
    inference(resolution,[status(thm)],[c_52,c_2054])).

tff(c_2706,plain,(
    ! [A_243,B_244,E_245] :
      ( k1_partfun1(A_243,B_244,'#skF_1','#skF_2',E_245,'#skF_3') = k5_relat_1(E_245,'#skF_3')
      | ~ m1_subset_1(E_245,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244)))
      | ~ v1_funct_1(E_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2078])).

tff(c_2752,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2706])).

tff(c_2771,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1658,c_2752])).

tff(c_207,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_72,B_73)),k2_relat_1(B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_72,B_73] :
      ( k2_relat_1(k5_relat_1(A_72,B_73)) = k2_relat_1(B_73)
      | ~ r1_tarski(k2_relat_1(B_73),k2_relat_1(k5_relat_1(A_72,B_73)))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_2789,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2771,c_217])).

tff(c_2796,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_148,c_357,c_57,c_57,c_2771,c_2789])).

tff(c_2798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_266,c_2796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:20:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.94  
% 4.68/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.95  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.68/1.95  
% 4.68/1.95  %Foreground sorts:
% 4.68/1.95  
% 4.68/1.95  
% 4.68/1.95  %Background operators:
% 4.68/1.95  
% 4.68/1.95  
% 4.68/1.95  %Foreground operators:
% 4.68/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.68/1.95  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.68/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.95  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.68/1.95  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.68/1.95  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.68/1.95  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.95  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.68/1.95  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.95  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.68/1.95  tff('#skF_3', type, '#skF_3': $i).
% 4.68/1.95  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.95  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.68/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.68/1.95  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.68/1.95  tff('#skF_4', type, '#skF_4': $i).
% 4.68/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.68/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.68/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.95  
% 4.68/1.96  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 4.68/1.96  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.68/1.96  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.68/1.96  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.68/1.96  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.68/1.96  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.68/1.96  tff(f_99, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.68/1.96  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.68/1.96  tff(f_75, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.68/1.96  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.68/1.96  tff(f_97, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.68/1.96  tff(f_87, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 4.68/1.96  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.68/1.96  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 4.68/1.96  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.68/1.96  tff(c_52, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.68/1.96  tff(c_234, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.96  tff(c_252, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_52, c_234])).
% 4.68/1.96  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.68/1.96  tff(c_266, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_42])).
% 4.68/1.96  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.68/1.96  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.68/1.96  tff(c_126, plain, (![B_60, A_61]: (v1_relat_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_61)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.68/1.96  tff(c_135, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_126])).
% 4.68/1.96  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_135])).
% 4.68/1.96  tff(c_138, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_126])).
% 4.68/1.96  tff(c_148, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_138])).
% 4.68/1.96  tff(c_297, plain, (![A_87, B_88, C_89]: (m1_subset_1(k2_relset_1(A_87, B_88, C_89), k1_zfmisc_1(B_88)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/1.96  tff(c_313, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_252, c_297])).
% 4.68/1.96  tff(c_325, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_313])).
% 4.68/1.96  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.96  tff(c_357, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_325, c_8])).
% 4.68/1.96  tff(c_40, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.68/1.96  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.68/1.96  tff(c_57, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 4.68/1.96  tff(c_50, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.68/1.96  tff(c_465, plain, (![C_105, B_102, F_104, E_106, D_101, A_103]: (k4_relset_1(A_103, B_102, C_105, D_101, E_106, F_104)=k5_relat_1(E_106, F_104) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(C_105, D_101))) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.68/1.96  tff(c_647, plain, (![A_124, B_125, E_126]: (k4_relset_1(A_124, B_125, '#skF_1', '#skF_2', E_126, '#skF_3')=k5_relat_1(E_126, '#skF_3') | ~m1_subset_1(E_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(resolution, [status(thm)], [c_52, c_465])).
% 4.68/1.96  tff(c_686, plain, (k4_relset_1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_647])).
% 4.68/1.96  tff(c_24, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (m1_subset_1(k4_relset_1(A_17, B_18, C_19, D_20, E_21, F_22), k1_zfmisc_1(k2_zfmisc_1(A_17, D_20))) | ~m1_subset_1(F_22, k1_zfmisc_1(k2_zfmisc_1(C_19, D_20))) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.68/1.96  tff(c_804, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_686, c_24])).
% 4.68/1.96  tff(c_808, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52, c_804])).
% 4.68/1.96  tff(c_56, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.68/1.96  tff(c_749, plain, (![D_130, F_129, C_132, A_127, E_131, B_128]: (k1_partfun1(A_127, B_128, C_132, D_130, E_131, F_129)=k5_relat_1(E_131, F_129) | ~m1_subset_1(F_129, k1_zfmisc_1(k2_zfmisc_1(C_132, D_130))) | ~v1_funct_1(F_129) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.68/1.96  tff(c_773, plain, (![A_127, B_128, E_131]: (k1_partfun1(A_127, B_128, '#skF_1', '#skF_2', E_131, '#skF_3')=k5_relat_1(E_131, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_52, c_749])).
% 4.68/1.96  tff(c_1580, plain, (![A_171, B_172, E_173]: (k1_partfun1(A_171, B_172, '#skF_1', '#skF_2', E_173, '#skF_3')=k5_relat_1(E_173, '#skF_3') | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_1(E_173))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_773])).
% 4.68/1.96  tff(c_1629, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_1580])).
% 4.68/1.96  tff(c_1649, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1629])).
% 4.68/1.96  tff(c_36, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.96  tff(c_44, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.68/1.96  tff(c_384, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.68/1.96  tff(c_394, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_44, c_384])).
% 4.68/1.97  tff(c_413, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_394])).
% 4.68/1.97  tff(c_414, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_413])).
% 4.68/1.97  tff(c_1653, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1649, c_414])).
% 4.68/1.97  tff(c_1657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_808, c_1653])).
% 4.68/1.97  tff(c_1658, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_413])).
% 4.68/1.97  tff(c_2054, plain, (![E_216, F_214, D_215, C_217, B_213, A_212]: (k1_partfun1(A_212, B_213, C_217, D_215, E_216, F_214)=k5_relat_1(E_216, F_214) | ~m1_subset_1(F_214, k1_zfmisc_1(k2_zfmisc_1(C_217, D_215))) | ~v1_funct_1(F_214) | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_1(E_216))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.68/1.97  tff(c_2078, plain, (![A_212, B_213, E_216]: (k1_partfun1(A_212, B_213, '#skF_1', '#skF_2', E_216, '#skF_3')=k5_relat_1(E_216, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_216, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))) | ~v1_funct_1(E_216))), inference(resolution, [status(thm)], [c_52, c_2054])).
% 4.68/1.97  tff(c_2706, plain, (![A_243, B_244, E_245]: (k1_partfun1(A_243, B_244, '#skF_1', '#skF_2', E_245, '#skF_3')=k5_relat_1(E_245, '#skF_3') | ~m1_subset_1(E_245, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))) | ~v1_funct_1(E_245))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2078])).
% 4.68/1.97  tff(c_2752, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2706])).
% 4.68/1.97  tff(c_2771, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1658, c_2752])).
% 4.68/1.97  tff(c_207, plain, (![A_72, B_73]: (r1_tarski(k2_relat_1(k5_relat_1(A_72, B_73)), k2_relat_1(B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.68/1.97  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.97  tff(c_217, plain, (![A_72, B_73]: (k2_relat_1(k5_relat_1(A_72, B_73))=k2_relat_1(B_73) | ~r1_tarski(k2_relat_1(B_73), k2_relat_1(k5_relat_1(A_72, B_73))) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_207, c_2])).
% 4.68/1.97  tff(c_2789, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2771, c_217])).
% 4.68/1.97  tff(c_2796, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_145, c_148, c_357, c_57, c_57, c_2771, c_2789])).
% 4.68/1.97  tff(c_2798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_266, c_2796])).
% 4.68/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.97  
% 4.68/1.97  Inference rules
% 4.68/1.97  ----------------------
% 4.68/1.97  #Ref     : 0
% 4.68/1.97  #Sup     : 652
% 4.68/1.97  #Fact    : 0
% 4.68/1.97  #Define  : 0
% 4.68/1.97  #Split   : 7
% 4.68/1.97  #Chain   : 0
% 4.68/1.97  #Close   : 0
% 4.68/1.97  
% 4.68/1.97  Ordering : KBO
% 4.68/1.97  
% 4.68/1.97  Simplification rules
% 4.68/1.97  ----------------------
% 4.68/1.97  #Subsume      : 50
% 4.68/1.97  #Demod        : 233
% 4.68/1.97  #Tautology    : 154
% 4.68/1.97  #SimpNegUnit  : 2
% 4.68/1.97  #BackRed      : 17
% 4.68/1.97  
% 4.68/1.97  #Partial instantiations: 0
% 4.68/1.97  #Strategies tried      : 1
% 4.68/1.97  
% 4.68/1.97  Timing (in seconds)
% 4.68/1.97  ----------------------
% 4.68/1.97  Preprocessing        : 0.35
% 4.68/1.97  Parsing              : 0.19
% 4.68/1.97  CNF conversion       : 0.02
% 4.68/1.97  Main loop            : 0.78
% 4.68/1.97  Inferencing          : 0.27
% 4.68/1.97  Reduction            : 0.28
% 4.68/1.97  Demodulation         : 0.20
% 4.68/1.97  BG Simplification    : 0.03
% 4.68/1.97  Subsumption          : 0.13
% 4.68/1.97  Abstraction          : 0.05
% 4.68/1.97  MUC search           : 0.00
% 4.68/1.97  Cooper               : 0.00
% 4.68/1.97  Total                : 1.17
% 4.68/1.97  Index Insertion      : 0.00
% 4.68/1.97  Index Deletion       : 0.00
% 4.68/1.97  Index Matching       : 0.00
% 4.68/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
