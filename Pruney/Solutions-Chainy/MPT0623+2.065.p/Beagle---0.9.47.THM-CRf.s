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
% DateTime   : Thu Dec  3 10:03:14 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 146 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 356 expanded)
%              Number of equality atoms :   73 ( 192 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(np__1,type,(
    np__1: $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_82,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_42,plain,(
    ! [A_28] : v1_relat_1('#skF_5'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_40,plain,(
    ! [A_28] : v1_funct_1('#skF_5'(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_38,plain,(
    ! [A_28] : k1_relat_1('#skF_5'(A_28)) = A_28 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_75,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_404,plain,(
    ! [A_108,B_109] :
      ( r2_hidden(k4_tarski('#skF_2'(A_108,B_109),'#skF_1'(A_108,B_109)),A_108)
      | r2_hidden('#skF_3'(A_108,B_109),B_109)
      | k2_relat_1(A_108) = B_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_104])).

tff(c_443,plain,(
    ! [B_109] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_109),B_109)
      | k2_relat_1(k1_xboole_0) = B_109 ) ),
    inference(resolution,[status(thm)],[c_404,c_110])).

tff(c_455,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_110),B_110)
      | k1_xboole_0 = B_110 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_443])).

tff(c_46,plain,(
    ! [A_34,B_38] :
      ( k1_relat_1('#skF_6'(A_34,B_38)) = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [A_34,B_38] :
      ( v1_funct_1('#skF_6'(A_34,B_38))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [A_34,B_38] :
      ( v1_relat_1('#skF_6'(A_34,B_38))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(k1_tarski(A_2),B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_188,plain,(
    ! [A_69,B_70] :
      ( k2_relat_1('#skF_6'(A_69,B_70)) = k1_tarski(B_70)
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    ! [C_41] :
      ( ~ r1_tarski(k2_relat_1(C_41),'#skF_7')
      | k1_relat_1(C_41) != '#skF_8'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_200,plain,(
    ! [B_71,A_72] :
      ( ~ r1_tarski(k1_tarski(B_71),'#skF_7')
      | k1_relat_1('#skF_6'(A_72,B_71)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_72,B_71))
      | ~ v1_relat_1('#skF_6'(A_72,B_71))
      | k1_xboole_0 = A_72 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_52])).

tff(c_269,plain,(
    ! [A_87,A_88] :
      ( k1_relat_1('#skF_6'(A_87,A_88)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_87,A_88))
      | ~ v1_relat_1('#skF_6'(A_87,A_88))
      | k1_xboole_0 = A_87
      | ~ r2_hidden(A_88,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6,c_200])).

tff(c_305,plain,(
    ! [A_93,B_94] :
      ( k1_relat_1('#skF_6'(A_93,B_94)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_93,B_94))
      | ~ r2_hidden(B_94,'#skF_7')
      | k1_xboole_0 = A_93 ) ),
    inference(resolution,[status(thm)],[c_50,c_269])).

tff(c_310,plain,(
    ! [A_95,B_96] :
      ( k1_relat_1('#skF_6'(A_95,B_96)) != '#skF_8'
      | ~ r2_hidden(B_96,'#skF_7')
      | k1_xboole_0 = A_95 ) ),
    inference(resolution,[status(thm)],[c_48,c_305])).

tff(c_313,plain,(
    ! [A_34,B_38] :
      ( A_34 != '#skF_8'
      | ~ r2_hidden(B_38,'#skF_7')
      | k1_xboole_0 = A_34
      | k1_xboole_0 = A_34 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_310])).

tff(c_315,plain,(
    ! [B_38] : ~ r2_hidden(B_38,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_487,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_455,c_315])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_487])).

tff(c_504,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_64] :
      ( k2_relat_1(A_64) = k1_xboole_0
      | k1_relat_1(A_64) != k1_xboole_0
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_148,plain,(
    ! [A_28] :
      ( k2_relat_1('#skF_5'(A_28)) = k1_xboole_0
      | k1_relat_1('#skF_5'(A_28)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_142])).

tff(c_153,plain,(
    ! [A_65] :
      ( k2_relat_1('#skF_5'(A_65)) = k1_xboole_0
      | k1_xboole_0 != A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_148])).

tff(c_159,plain,(
    ! [A_65] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_7')
      | k1_relat_1('#skF_5'(A_65)) != '#skF_8'
      | ~ v1_funct_1('#skF_5'(A_65))
      | ~ v1_relat_1('#skF_5'(A_65))
      | k1_xboole_0 != A_65 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_52])).

tff(c_165,plain,(
    ! [A_65] :
      ( A_65 != '#skF_8'
      | k1_xboole_0 != A_65 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_2,c_159])).

tff(c_170,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_165])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_170])).

tff(c_532,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_535,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_2])).

tff(c_34,plain,(
    ! [A_27] :
      ( k2_relat_1(A_27) = k1_xboole_0
      | k1_relat_1(A_27) != k1_xboole_0
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_670,plain,(
    ! [A_139] :
      ( k2_relat_1(A_139) = '#skF_8'
      | k1_relat_1(A_139) != '#skF_8'
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_532,c_34])).

tff(c_676,plain,(
    ! [A_28] :
      ( k2_relat_1('#skF_5'(A_28)) = '#skF_8'
      | k1_relat_1('#skF_5'(A_28)) != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_42,c_670])).

tff(c_681,plain,(
    ! [A_140] :
      ( k2_relat_1('#skF_5'(A_140)) = '#skF_8'
      | A_140 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_676])).

tff(c_533,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_542,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_533])).

tff(c_543,plain,(
    ! [C_41] :
      ( ~ r1_tarski(k2_relat_1(C_41),'#skF_8')
      | k1_relat_1(C_41) != '#skF_8'
      | ~ v1_funct_1(C_41)
      | ~ v1_relat_1(C_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_52])).

tff(c_690,plain,(
    ! [A_140] :
      ( ~ r1_tarski('#skF_8','#skF_8')
      | k1_relat_1('#skF_5'(A_140)) != '#skF_8'
      | ~ v1_funct_1('#skF_5'(A_140))
      | ~ v1_relat_1('#skF_5'(A_140))
      | A_140 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_543])).

tff(c_697,plain,(
    ! [A_140] : A_140 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_535,c_690])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_565,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_8',B_5) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_532,c_12])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:47:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.38  
% 2.87/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.38  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > np__1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1
% 2.87/1.38  
% 2.87/1.38  %Foreground sorts:
% 2.87/1.38  
% 2.87/1.38  
% 2.87/1.38  %Background operators:
% 2.87/1.38  
% 2.87/1.38  
% 2.87/1.38  %Foreground operators:
% 2.87/1.38  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.87/1.38  tff(np__1, type, np__1: $i).
% 2.87/1.38  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.87/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.87/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.87/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.38  
% 2.87/1.39  tff(f_69, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 2.87/1.39  tff(f_100, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 2.87/1.39  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.87/1.39  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.87/1.39  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.87/1.39  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.87/1.39  tff(f_82, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_funct_1)).
% 2.87/1.39  tff(f_31, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.87/1.39  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.87/1.39  tff(f_57, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.87/1.39  tff(c_42, plain, (![A_28]: (v1_relat_1('#skF_5'(A_28)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.87/1.39  tff(c_40, plain, (![A_28]: (v1_funct_1('#skF_5'(A_28)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.87/1.39  tff(c_38, plain, (![A_28]: (k1_relat_1('#skF_5'(A_28))=A_28)), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.87/1.39  tff(c_54, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.39  tff(c_75, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_54])).
% 2.87/1.39  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.87/1.39  tff(c_404, plain, (![A_108, B_109]: (r2_hidden(k4_tarski('#skF_2'(A_108, B_109), '#skF_1'(A_108, B_109)), A_108) | r2_hidden('#skF_3'(A_108, B_109), B_109) | k2_relat_1(A_108)=B_109)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.87/1.39  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.39  tff(c_104, plain, (![A_49, B_50]: (~r2_hidden(A_49, k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.87/1.39  tff(c_110, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_104])).
% 2.87/1.39  tff(c_443, plain, (![B_109]: (r2_hidden('#skF_3'(k1_xboole_0, B_109), B_109) | k2_relat_1(k1_xboole_0)=B_109)), inference(resolution, [status(thm)], [c_404, c_110])).
% 2.87/1.39  tff(c_455, plain, (![B_110]: (r2_hidden('#skF_3'(k1_xboole_0, B_110), B_110) | k1_xboole_0=B_110)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_443])).
% 2.87/1.39  tff(c_46, plain, (![A_34, B_38]: (k1_relat_1('#skF_6'(A_34, B_38))=A_34 | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.87/1.39  tff(c_48, plain, (![A_34, B_38]: (v1_funct_1('#skF_6'(A_34, B_38)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.87/1.39  tff(c_50, plain, (![A_34, B_38]: (v1_relat_1('#skF_6'(A_34, B_38)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.87/1.39  tff(c_6, plain, (![A_2, B_3]: (r1_tarski(k1_tarski(A_2), B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.39  tff(c_188, plain, (![A_69, B_70]: (k2_relat_1('#skF_6'(A_69, B_70))=k1_tarski(B_70) | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.87/1.39  tff(c_52, plain, (![C_41]: (~r1_tarski(k2_relat_1(C_41), '#skF_7') | k1_relat_1(C_41)!='#skF_8' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.87/1.39  tff(c_200, plain, (![B_71, A_72]: (~r1_tarski(k1_tarski(B_71), '#skF_7') | k1_relat_1('#skF_6'(A_72, B_71))!='#skF_8' | ~v1_funct_1('#skF_6'(A_72, B_71)) | ~v1_relat_1('#skF_6'(A_72, B_71)) | k1_xboole_0=A_72)), inference(superposition, [status(thm), theory('equality')], [c_188, c_52])).
% 2.87/1.39  tff(c_269, plain, (![A_87, A_88]: (k1_relat_1('#skF_6'(A_87, A_88))!='#skF_8' | ~v1_funct_1('#skF_6'(A_87, A_88)) | ~v1_relat_1('#skF_6'(A_87, A_88)) | k1_xboole_0=A_87 | ~r2_hidden(A_88, '#skF_7'))), inference(resolution, [status(thm)], [c_6, c_200])).
% 2.87/1.39  tff(c_305, plain, (![A_93, B_94]: (k1_relat_1('#skF_6'(A_93, B_94))!='#skF_8' | ~v1_funct_1('#skF_6'(A_93, B_94)) | ~r2_hidden(B_94, '#skF_7') | k1_xboole_0=A_93)), inference(resolution, [status(thm)], [c_50, c_269])).
% 2.87/1.39  tff(c_310, plain, (![A_95, B_96]: (k1_relat_1('#skF_6'(A_95, B_96))!='#skF_8' | ~r2_hidden(B_96, '#skF_7') | k1_xboole_0=A_95)), inference(resolution, [status(thm)], [c_48, c_305])).
% 2.87/1.39  tff(c_313, plain, (![A_34, B_38]: (A_34!='#skF_8' | ~r2_hidden(B_38, '#skF_7') | k1_xboole_0=A_34 | k1_xboole_0=A_34)), inference(superposition, [status(thm), theory('equality')], [c_46, c_310])).
% 2.87/1.39  tff(c_315, plain, (![B_38]: (~r2_hidden(B_38, '#skF_7'))), inference(splitLeft, [status(thm)], [c_313])).
% 2.87/1.39  tff(c_487, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_455, c_315])).
% 2.87/1.39  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_487])).
% 2.87/1.39  tff(c_504, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_313])).
% 2.87/1.39  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.39  tff(c_142, plain, (![A_64]: (k2_relat_1(A_64)=k1_xboole_0 | k1_relat_1(A_64)!=k1_xboole_0 | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.39  tff(c_148, plain, (![A_28]: (k2_relat_1('#skF_5'(A_28))=k1_xboole_0 | k1_relat_1('#skF_5'(A_28))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_142])).
% 2.87/1.39  tff(c_153, plain, (![A_65]: (k2_relat_1('#skF_5'(A_65))=k1_xboole_0 | k1_xboole_0!=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_148])).
% 2.87/1.39  tff(c_159, plain, (![A_65]: (~r1_tarski(k1_xboole_0, '#skF_7') | k1_relat_1('#skF_5'(A_65))!='#skF_8' | ~v1_funct_1('#skF_5'(A_65)) | ~v1_relat_1('#skF_5'(A_65)) | k1_xboole_0!=A_65)), inference(superposition, [status(thm), theory('equality')], [c_153, c_52])).
% 2.87/1.39  tff(c_165, plain, (![A_65]: (A_65!='#skF_8' | k1_xboole_0!=A_65)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_2, c_159])).
% 2.87/1.39  tff(c_170, plain, (k1_xboole_0!='#skF_8'), inference(reflexivity, [status(thm), theory('equality')], [c_165])).
% 2.87/1.39  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_504, c_170])).
% 2.87/1.39  tff(c_532, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_54])).
% 2.87/1.39  tff(c_535, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_2])).
% 2.87/1.39  tff(c_34, plain, (![A_27]: (k2_relat_1(A_27)=k1_xboole_0 | k1_relat_1(A_27)!=k1_xboole_0 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.87/1.39  tff(c_670, plain, (![A_139]: (k2_relat_1(A_139)='#skF_8' | k1_relat_1(A_139)!='#skF_8' | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_532, c_532, c_34])).
% 2.87/1.39  tff(c_676, plain, (![A_28]: (k2_relat_1('#skF_5'(A_28))='#skF_8' | k1_relat_1('#skF_5'(A_28))!='#skF_8')), inference(resolution, [status(thm)], [c_42, c_670])).
% 2.87/1.39  tff(c_681, plain, (![A_140]: (k2_relat_1('#skF_5'(A_140))='#skF_8' | A_140!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_676])).
% 2.87/1.39  tff(c_533, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_54])).
% 2.87/1.39  tff(c_542, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_532, c_533])).
% 2.87/1.39  tff(c_543, plain, (![C_41]: (~r1_tarski(k2_relat_1(C_41), '#skF_8') | k1_relat_1(C_41)!='#skF_8' | ~v1_funct_1(C_41) | ~v1_relat_1(C_41))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_52])).
% 2.87/1.39  tff(c_690, plain, (![A_140]: (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_5'(A_140))!='#skF_8' | ~v1_funct_1('#skF_5'(A_140)) | ~v1_relat_1('#skF_5'(A_140)) | A_140!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_681, c_543])).
% 2.87/1.39  tff(c_697, plain, (![A_140]: (A_140!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_535, c_690])).
% 2.87/1.39  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.87/1.39  tff(c_565, plain, (![B_5]: (k2_zfmisc_1('#skF_8', B_5)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_532, c_532, c_12])).
% 2.87/1.39  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_697, c_565])).
% 2.87/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.39  
% 2.87/1.39  Inference rules
% 2.87/1.39  ----------------------
% 2.87/1.39  #Ref     : 1
% 2.87/1.39  #Sup     : 127
% 2.87/1.39  #Fact    : 0
% 2.87/1.39  #Define  : 0
% 2.87/1.39  #Split   : 5
% 2.87/1.39  #Chain   : 0
% 2.87/1.39  #Close   : 0
% 2.87/1.39  
% 2.87/1.39  Ordering : KBO
% 2.87/1.39  
% 2.87/1.39  Simplification rules
% 2.87/1.39  ----------------------
% 2.87/1.39  #Subsume      : 28
% 2.87/1.39  #Demod        : 83
% 2.87/1.39  #Tautology    : 57
% 2.87/1.39  #SimpNegUnit  : 20
% 2.87/1.39  #BackRed      : 39
% 2.87/1.39  
% 2.87/1.40  #Partial instantiations: 0
% 2.87/1.40  #Strategies tried      : 1
% 2.87/1.40  
% 2.87/1.40  Timing (in seconds)
% 2.87/1.40  ----------------------
% 2.87/1.40  Preprocessing        : 0.30
% 2.87/1.40  Parsing              : 0.16
% 2.87/1.40  CNF conversion       : 0.02
% 2.87/1.40  Main loop            : 0.30
% 2.87/1.40  Inferencing          : 0.11
% 2.87/1.40  Reduction            : 0.08
% 2.87/1.40  Demodulation         : 0.06
% 2.87/1.40  BG Simplification    : 0.02
% 2.87/1.40  Subsumption          : 0.05
% 2.87/1.40  Abstraction          : 0.01
% 2.87/1.40  MUC search           : 0.00
% 2.87/1.40  Cooper               : 0.00
% 2.87/1.40  Total                : 0.64
% 2.87/1.40  Index Insertion      : 0.00
% 2.87/1.40  Index Deletion       : 0.00
% 2.87/1.40  Index Matching       : 0.00
% 2.87/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
