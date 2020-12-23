%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:55 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 269 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  159 ( 681 expanded)
%              Number of equality atoms :   63 ( 218 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( r2_hidden(B,A)
         => ( r2_hidden(B,k8_setfam_1(A,C))
          <=> ! [D] :
                ( r2_hidden(D,C)
               => r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_40,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_366,plain,(
    ! [A_76,B_77] :
      ( k6_setfam_1(A_76,B_77) = k1_setfam_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_374,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_366])).

tff(c_477,plain,(
    ! [A_95,B_96] :
      ( k8_setfam_1(A_95,B_96) = k6_setfam_1(A_95,B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(k1_zfmisc_1(A_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_480,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_477])).

tff(c_486,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_480])).

tff(c_490,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_486])).

tff(c_8,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5] :
      ( k8_setfam_1(A_5,k1_xboole_0) = A_5
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_5] : k8_setfam_1(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_499,plain,(
    ! [A_5] : k8_setfam_1(A_5,'#skF_7') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_490,c_57])).

tff(c_46,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_529,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_499,c_79])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_529])).

tff(c_533,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_535,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_79])).

tff(c_534,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_486])).

tff(c_440,plain,(
    ! [A_91,C_92] :
      ( r2_hidden('#skF_1'(A_91,k1_setfam_1(A_91),C_92),A_91)
      | r2_hidden(C_92,k1_setfam_1(A_91))
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_52,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_8','#skF_7')
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_112,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_195,plain,(
    ! [C_59,D_60,A_61] :
      ( r2_hidden(C_59,D_60)
      | ~ r2_hidden(D_60,A_61)
      | ~ r2_hidden(C_59,k1_setfam_1(A_61))
      | k1_xboole_0 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_203,plain,(
    ! [C_59] :
      ( r2_hidden(C_59,'#skF_8')
      | ~ r2_hidden(C_59,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_112,c_195])).

tff(c_230,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_203])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [B_37,A_38] :
      ( ~ r2_hidden(B_37,A_38)
      | k4_xboole_0(A_38,k1_tarski(B_37)) != A_38 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [B_37] : ~ r2_hidden(B_37,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_80])).

tff(c_234,plain,(
    ! [B_37] : ~ r2_hidden(B_37,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_85])).

tff(c_249,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_112])).

tff(c_251,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_203])).

tff(c_170,plain,(
    ! [A_56,B_57] :
      ( k6_setfam_1(A_56,B_57) = k1_setfam_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_178,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_170])).

tff(c_317,plain,(
    ! [A_69,B_70] :
      ( k8_setfam_1(A_69,B_70) = k6_setfam_1(A_69,B_70)
      | k1_xboole_0 = B_70
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_320,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_317])).

tff(c_326,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_320])).

tff(c_327,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_326])).

tff(c_331,plain,(
    ~ r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_79])).

tff(c_252,plain,(
    ! [A_65,C_66] :
      ( r2_hidden('#skF_1'(A_65,k1_setfam_1(A_65),C_66),A_65)
      | r2_hidden(C_66,k1_setfam_1(A_65))
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_50,plain,(
    ! [D_33] :
      ( ~ r2_hidden('#skF_6','#skF_8')
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_113,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7'))
      | r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_133,plain,(
    ! [D_48] :
      ( r2_hidden('#skF_6',D_48)
      | ~ r2_hidden(D_48,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_54])).

tff(c_135,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_112,c_133])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_135])).

tff(c_140,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_274,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_66))
      | r2_hidden(C_66,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_252,c_140])).

tff(c_342,plain,(
    ! [C_66] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_66))
      | r2_hidden(C_66,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_274])).

tff(c_351,plain,(
    ! [C_73,A_74] :
      ( ~ r2_hidden(C_73,'#skF_1'(A_74,k1_setfam_1(A_74),C_73))
      | r2_hidden(C_73,k1_setfam_1(A_74))
      | k1_xboole_0 = A_74 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_355,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_342,c_351])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_331,c_251,c_331,c_355])).

tff(c_363,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_6',D_33)
      | ~ r2_hidden(D_33,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_462,plain,(
    ! [C_92] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_92))
      | r2_hidden(C_92,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_440,c_363])).

tff(c_562,plain,(
    ! [C_103] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_7',k1_setfam_1('#skF_7'),C_103))
      | r2_hidden(C_103,k1_setfam_1('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_534,c_462])).

tff(c_28,plain,(
    ! [C_19,A_7] :
      ( ~ r2_hidden(C_19,'#skF_1'(A_7,k1_setfam_1(A_7),C_19))
      | r2_hidden(C_19,k1_setfam_1(A_7))
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_566,plain,
    ( k1_xboole_0 = '#skF_7'
    | r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_562,c_28])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_535,c_534,c_535,c_566])).

tff(c_576,plain,(
    r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6',k8_setfam_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_578,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_44])).

tff(c_575,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_659,plain,(
    ! [C_118,D_119,A_120] :
      ( r2_hidden(C_118,D_119)
      | ~ r2_hidden(D_119,A_120)
      | ~ r2_hidden(C_118,k1_setfam_1(A_120))
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_667,plain,(
    ! [C_118] :
      ( r2_hidden(C_118,'#skF_8')
      | ~ r2_hidden(C_118,k1_setfam_1('#skF_7'))
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_575,c_659])).

tff(c_686,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_579,plain,(
    ! [B_104,A_105] :
      ( ~ r2_hidden(B_104,A_105)
      | k4_xboole_0(A_105,k1_tarski(B_104)) != A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_584,plain,(
    ! [B_104] : ~ r2_hidden(B_104,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_579])).

tff(c_704,plain,(
    ! [B_104] : ~ r2_hidden(B_104,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_584])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_704,c_575])).

tff(c_725,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_637,plain,(
    ! [A_115,B_116] :
      ( k6_setfam_1(A_115,B_116) = k1_setfam_1(B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(k1_zfmisc_1(A_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_645,plain,(
    k6_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_637])).

tff(c_727,plain,(
    ! [A_125,B_126] :
      ( k8_setfam_1(A_125,B_126) = k6_setfam_1(A_125,B_126)
      | k1_xboole_0 = B_126
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k1_zfmisc_1(A_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_730,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k6_setfam_1('#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_727])).

tff(c_736,plain,
    ( k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_730])).

tff(c_737,plain,(
    k8_setfam_1('#skF_5','#skF_7') = k1_setfam_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_725,c_736])).

tff(c_742,plain,(
    r2_hidden('#skF_6',k1_setfam_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_576])).

tff(c_724,plain,(
    ! [C_118] :
      ( r2_hidden(C_118,'#skF_8')
      | ~ r2_hidden(C_118,k1_setfam_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_756,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_742,c_724])).

tff(c_764,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_578,c_756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.40  
% 2.83/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.41  %$ r2_hidden > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_8 > #skF_2 > #skF_4
% 2.83/1.41  
% 2.83/1.41  %Foreground sorts:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Background operators:
% 2.83/1.41  
% 2.83/1.41  
% 2.83/1.41  %Foreground operators:
% 2.83/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.83/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.83/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.83/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.41  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.83/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.83/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.83/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.83/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.41  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.83/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.83/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.83/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.83/1.41  
% 2.83/1.43  tff(f_86, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r2_hidden(B, A) => (r2_hidden(B, k8_setfam_1(A, C)) <=> (![D]: (r2_hidden(D, C) => r2_hidden(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_setfam_1)).
% 2.83/1.43  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.83/1.43  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.83/1.43  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.83/1.43  tff(f_64, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 2.83/1.43  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.83/1.43  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.83/1.43  tff(c_40, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_366, plain, (![A_76, B_77]: (k6_setfam_1(A_76, B_77)=k1_setfam_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.43  tff(c_374, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_366])).
% 2.83/1.43  tff(c_477, plain, (![A_95, B_96]: (k8_setfam_1(A_95, B_96)=k6_setfam_1(A_95, B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(k1_zfmisc_1(A_95))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.43  tff(c_480, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_477])).
% 2.83/1.43  tff(c_486, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_374, c_480])).
% 2.83/1.43  tff(c_490, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_486])).
% 2.83/1.43  tff(c_8, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.83/1.43  tff(c_10, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.43  tff(c_57, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.83/1.43  tff(c_499, plain, (![A_5]: (k8_setfam_1(A_5, '#skF_7')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_490, c_57])).
% 2.83/1.43  tff(c_46, plain, (r2_hidden('#skF_8', '#skF_7') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_79, plain, (~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitLeft, [status(thm)], [c_46])).
% 2.83/1.43  tff(c_529, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_499, c_79])).
% 2.83/1.43  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_529])).
% 2.83/1.43  tff(c_533, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(splitRight, [status(thm)], [c_486])).
% 2.83/1.43  tff(c_535, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_79])).
% 2.83/1.43  tff(c_534, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_486])).
% 2.83/1.43  tff(c_440, plain, (![A_91, C_92]: (r2_hidden('#skF_1'(A_91, k1_setfam_1(A_91), C_92), A_91) | r2_hidden(C_92, k1_setfam_1(A_91)) | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.43  tff(c_52, plain, (![D_33]: (r2_hidden('#skF_8', '#skF_7') | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_112, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitLeft, [status(thm)], [c_52])).
% 2.83/1.43  tff(c_195, plain, (![C_59, D_60, A_61]: (r2_hidden(C_59, D_60) | ~r2_hidden(D_60, A_61) | ~r2_hidden(C_59, k1_setfam_1(A_61)) | k1_xboole_0=A_61)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.43  tff(c_203, plain, (![C_59]: (r2_hidden(C_59, '#skF_8') | ~r2_hidden(C_59, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_112, c_195])).
% 2.83/1.43  tff(c_230, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_203])).
% 2.83/1.43  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.43  tff(c_80, plain, (![B_37, A_38]: (~r2_hidden(B_37, A_38) | k4_xboole_0(A_38, k1_tarski(B_37))!=A_38)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.43  tff(c_85, plain, (![B_37]: (~r2_hidden(B_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_80])).
% 2.83/1.43  tff(c_234, plain, (![B_37]: (~r2_hidden(B_37, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_230, c_85])).
% 2.83/1.43  tff(c_249, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_112])).
% 2.83/1.43  tff(c_251, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_203])).
% 2.83/1.43  tff(c_170, plain, (![A_56, B_57]: (k6_setfam_1(A_56, B_57)=k1_setfam_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.43  tff(c_178, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_170])).
% 2.83/1.43  tff(c_317, plain, (![A_69, B_70]: (k8_setfam_1(A_69, B_70)=k6_setfam_1(A_69, B_70) | k1_xboole_0=B_70 | ~m1_subset_1(B_70, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.43  tff(c_320, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_317])).
% 2.83/1.43  tff(c_326, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_320])).
% 2.83/1.43  tff(c_327, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_251, c_326])).
% 2.83/1.43  tff(c_331, plain, (~r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_79])).
% 2.83/1.43  tff(c_252, plain, (![A_65, C_66]: (r2_hidden('#skF_1'(A_65, k1_setfam_1(A_65), C_66), A_65) | r2_hidden(C_66, k1_setfam_1(A_65)) | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.43  tff(c_50, plain, (![D_33]: (~r2_hidden('#skF_6', '#skF_8') | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_113, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_50])).
% 2.83/1.43  tff(c_54, plain, (![D_33]: (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7')) | r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_133, plain, (![D_48]: (r2_hidden('#skF_6', D_48) | ~r2_hidden(D_48, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_79, c_54])).
% 2.83/1.43  tff(c_135, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_112, c_133])).
% 2.83/1.43  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_135])).
% 2.83/1.43  tff(c_140, plain, (![D_33]: (r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(splitRight, [status(thm)], [c_50])).
% 2.83/1.43  tff(c_274, plain, (![C_66]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_66)) | r2_hidden(C_66, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_252, c_140])).
% 2.83/1.43  tff(c_342, plain, (![C_66]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_66)) | r2_hidden(C_66, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_251, c_274])).
% 2.83/1.43  tff(c_351, plain, (![C_73, A_74]: (~r2_hidden(C_73, '#skF_1'(A_74, k1_setfam_1(A_74), C_73)) | r2_hidden(C_73, k1_setfam_1(A_74)) | k1_xboole_0=A_74)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.43  tff(c_355, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_342, c_351])).
% 2.83/1.43  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_331, c_251, c_331, c_355])).
% 2.83/1.43  tff(c_363, plain, (![D_33]: (r2_hidden('#skF_6', D_33) | ~r2_hidden(D_33, '#skF_7'))), inference(splitRight, [status(thm)], [c_52])).
% 2.83/1.43  tff(c_462, plain, (![C_92]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_92)) | r2_hidden(C_92, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_440, c_363])).
% 2.83/1.43  tff(c_562, plain, (![C_103]: (r2_hidden('#skF_6', '#skF_1'('#skF_7', k1_setfam_1('#skF_7'), C_103)) | r2_hidden(C_103, k1_setfam_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_534, c_462])).
% 2.83/1.43  tff(c_28, plain, (![C_19, A_7]: (~r2_hidden(C_19, '#skF_1'(A_7, k1_setfam_1(A_7), C_19)) | r2_hidden(C_19, k1_setfam_1(A_7)) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.43  tff(c_566, plain, (k1_xboole_0='#skF_7' | r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(resolution, [status(thm)], [c_562, c_28])).
% 2.83/1.43  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_535, c_534, c_535, c_566])).
% 2.83/1.43  tff(c_576, plain, (r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(splitRight, [status(thm)], [c_46])).
% 2.83/1.43  tff(c_44, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', k8_setfam_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.83/1.43  tff(c_578, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_576, c_44])).
% 2.83/1.43  tff(c_575, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_46])).
% 2.83/1.43  tff(c_659, plain, (![C_118, D_119, A_120]: (r2_hidden(C_118, D_119) | ~r2_hidden(D_119, A_120) | ~r2_hidden(C_118, k1_setfam_1(A_120)) | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.83/1.43  tff(c_667, plain, (![C_118]: (r2_hidden(C_118, '#skF_8') | ~r2_hidden(C_118, k1_setfam_1('#skF_7')) | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_575, c_659])).
% 2.83/1.43  tff(c_686, plain, (k1_xboole_0='#skF_7'), inference(splitLeft, [status(thm)], [c_667])).
% 2.83/1.43  tff(c_579, plain, (![B_104, A_105]: (~r2_hidden(B_104, A_105) | k4_xboole_0(A_105, k1_tarski(B_104))!=A_105)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.83/1.43  tff(c_584, plain, (![B_104]: (~r2_hidden(B_104, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_579])).
% 2.83/1.43  tff(c_704, plain, (![B_104]: (~r2_hidden(B_104, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_584])).
% 2.83/1.43  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_704, c_575])).
% 2.83/1.43  tff(c_725, plain, (k1_xboole_0!='#skF_7'), inference(splitRight, [status(thm)], [c_667])).
% 2.83/1.43  tff(c_637, plain, (![A_115, B_116]: (k6_setfam_1(A_115, B_116)=k1_setfam_1(B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(k1_zfmisc_1(A_115))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.83/1.43  tff(c_645, plain, (k6_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_637])).
% 2.83/1.43  tff(c_727, plain, (![A_125, B_126]: (k8_setfam_1(A_125, B_126)=k6_setfam_1(A_125, B_126) | k1_xboole_0=B_126 | ~m1_subset_1(B_126, k1_zfmisc_1(k1_zfmisc_1(A_125))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.83/1.43  tff(c_730, plain, (k8_setfam_1('#skF_5', '#skF_7')=k6_setfam_1('#skF_5', '#skF_7') | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_42, c_727])).
% 2.83/1.43  tff(c_736, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7') | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_645, c_730])).
% 2.83/1.43  tff(c_737, plain, (k8_setfam_1('#skF_5', '#skF_7')=k1_setfam_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_725, c_736])).
% 2.83/1.43  tff(c_742, plain, (r2_hidden('#skF_6', k1_setfam_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_737, c_576])).
% 2.83/1.43  tff(c_724, plain, (![C_118]: (r2_hidden(C_118, '#skF_8') | ~r2_hidden(C_118, k1_setfam_1('#skF_7')))), inference(splitRight, [status(thm)], [c_667])).
% 2.83/1.43  tff(c_756, plain, (r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_742, c_724])).
% 2.83/1.43  tff(c_764, plain, $false, inference(negUnitSimplification, [status(thm)], [c_578, c_756])).
% 2.83/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.43  
% 2.83/1.43  Inference rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Ref     : 0
% 2.83/1.43  #Sup     : 142
% 2.83/1.43  #Fact    : 0
% 2.83/1.43  #Define  : 0
% 2.83/1.43  #Split   : 15
% 2.83/1.43  #Chain   : 0
% 2.83/1.43  #Close   : 0
% 2.83/1.43  
% 2.83/1.43  Ordering : KBO
% 2.83/1.43  
% 2.83/1.43  Simplification rules
% 2.83/1.43  ----------------------
% 2.83/1.43  #Subsume      : 25
% 2.83/1.43  #Demod        : 129
% 2.83/1.43  #Tautology    : 79
% 2.83/1.43  #SimpNegUnit  : 30
% 2.83/1.43  #BackRed      : 76
% 2.83/1.43  
% 2.83/1.43  #Partial instantiations: 0
% 2.83/1.43  #Strategies tried      : 1
% 2.83/1.43  
% 2.83/1.43  Timing (in seconds)
% 2.83/1.43  ----------------------
% 3.11/1.43  Preprocessing        : 0.32
% 3.11/1.43  Parsing              : 0.15
% 3.11/1.43  CNF conversion       : 0.03
% 3.11/1.43  Main loop            : 0.34
% 3.11/1.43  Inferencing          : 0.11
% 3.11/1.43  Reduction            : 0.11
% 3.11/1.43  Demodulation         : 0.07
% 3.11/1.43  BG Simplification    : 0.02
% 3.11/1.43  Subsumption          : 0.07
% 3.11/1.43  Abstraction          : 0.02
% 3.11/1.43  MUC search           : 0.00
% 3.11/1.43  Cooper               : 0.00
% 3.11/1.43  Total                : 0.70
% 3.11/1.43  Index Insertion      : 0.00
% 3.11/1.43  Index Deletion       : 0.00
% 3.11/1.43  Index Matching       : 0.00
% 3.11/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
