%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:25 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 125 expanded)
%              Number of leaves         :   33 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 229 expanded)
%              Number of equality atoms :   35 (  81 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_51,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_42,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_100,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_relat_1(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_100])).

tff(c_28,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) = k1_xboole_0
      | k2_relat_1(A_27) != k1_xboole_0
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,
    ( k1_relat_1('#skF_7') = k1_xboole_0
    | k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_28])).

tff(c_119,plain,(
    k2_relat_1('#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_30,plain,(
    ! [A_27] :
      ( k2_relat_1(A_27) = k1_xboole_0
      | k1_relat_1(A_27) != k1_xboole_0
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_117,plain,
    ( k2_relat_1('#skF_7') = k1_xboole_0
    | k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_30])).

tff(c_120,plain,(
    k1_relat_1('#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_117])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_308,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(k4_tarski('#skF_2'(A_112,B_113),'#skF_1'(A_112,B_113)),A_112)
      | r2_hidden('#skF_3'(A_112,B_113),B_113)
      | k2_relat_1(A_112) = B_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ! [A_54,B_55] : ~ r2_hidden(A_54,k2_zfmisc_1(A_54,B_55)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_79])).

tff(c_323,plain,(
    ! [B_113] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_113),B_113)
      | k2_relat_1(k1_xboole_0) = B_113 ) ),
    inference(resolution,[status(thm)],[c_308,c_82])).

tff(c_329,plain,(
    ! [B_114] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_114),B_114)
      | k1_xboole_0 = B_114 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_323])).

tff(c_145,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,(
    k1_relset_1('#skF_6','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_145])).

tff(c_40,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k1_relset_1('#skF_6','#skF_5','#skF_7'))
      | ~ m1_subset_1(D_51,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_156,plain,(
    ! [D_51] :
      ( ~ r2_hidden(D_51,k1_relat_1('#skF_7'))
      | ~ m1_subset_1(D_51,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_40])).

tff(c_337,plain,
    ( ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_329,c_156])).

tff(c_347,plain,(
    ~ m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_337])).

tff(c_196,plain,(
    ! [A_92,B_93,C_94] :
      ( m1_subset_1(k1_relset_1(A_92,B_93,C_94),k1_zfmisc_1(A_92))
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_229,plain,
    ( m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_196])).

tff(c_245,plain,(
    m1_subset_1(k1_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_229])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_248,plain,(
    ! [A_5] :
      ( m1_subset_1(A_5,'#skF_6')
      | ~ r2_hidden(A_5,k1_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_245,c_10])).

tff(c_333,plain,
    ( m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6')
    | k1_relat_1('#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_329,c_248])).

tff(c_344,plain,(
    m1_subset_1('#skF_3'(k1_xboole_0,k1_relat_1('#skF_7')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_333])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_347,c_344])).

tff(c_352,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_401,plain,(
    ! [A_129,B_130,C_131] :
      ( k2_relset_1(A_129,B_130,C_131) = k2_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_404,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_44,c_401])).

tff(c_412,plain,(
    k2_relset_1('#skF_6','#skF_5','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_404])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:04:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  
% 2.15/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.32  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 2.15/1.32  
% 2.15/1.32  %Foreground sorts:
% 2.15/1.32  
% 2.15/1.32  
% 2.15/1.32  %Background operators:
% 2.15/1.32  
% 2.15/1.32  
% 2.15/1.32  %Foreground operators:
% 2.15/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.15/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.15/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.15/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.15/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.15/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.15/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.15/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.15/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.15/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.15/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.15/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.32  
% 2.55/1.34  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 2.55/1.34  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.34  tff(f_57, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 2.55/1.34  tff(f_51, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.55/1.34  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.55/1.34  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.55/1.34  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.55/1.34  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.55/1.34  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.55/1.34  tff(f_40, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.55/1.34  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.55/1.34  tff(c_42, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.55/1.34  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.55/1.34  tff(c_100, plain, (![C_61, A_62, B_63]: (v1_relat_1(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.34  tff(c_108, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_100])).
% 2.55/1.34  tff(c_28, plain, (![A_27]: (k1_relat_1(A_27)=k1_xboole_0 | k2_relat_1(A_27)!=k1_xboole_0 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.34  tff(c_116, plain, (k1_relat_1('#skF_7')=k1_xboole_0 | k2_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_28])).
% 2.55/1.34  tff(c_119, plain, (k2_relat_1('#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_116])).
% 2.55/1.34  tff(c_30, plain, (![A_27]: (k2_relat_1(A_27)=k1_xboole_0 | k1_relat_1(A_27)!=k1_xboole_0 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.34  tff(c_117, plain, (k2_relat_1('#skF_7')=k1_xboole_0 | k1_relat_1('#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_30])).
% 2.55/1.34  tff(c_120, plain, (k1_relat_1('#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_119, c_117])).
% 2.55/1.34  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.55/1.34  tff(c_308, plain, (![A_112, B_113]: (r2_hidden(k4_tarski('#skF_2'(A_112, B_113), '#skF_1'(A_112, B_113)), A_112) | r2_hidden('#skF_3'(A_112, B_113), B_113) | k2_relat_1(A_112)=B_113)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.55/1.34  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.55/1.34  tff(c_79, plain, (![A_54, B_55]: (~r2_hidden(A_54, k2_zfmisc_1(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.55/1.34  tff(c_82, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_79])).
% 2.55/1.34  tff(c_323, plain, (![B_113]: (r2_hidden('#skF_3'(k1_xboole_0, B_113), B_113) | k2_relat_1(k1_xboole_0)=B_113)), inference(resolution, [status(thm)], [c_308, c_82])).
% 2.55/1.34  tff(c_329, plain, (![B_114]: (r2_hidden('#skF_3'(k1_xboole_0, B_114), B_114) | k1_xboole_0=B_114)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_323])).
% 2.55/1.34  tff(c_145, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.55/1.34  tff(c_155, plain, (k1_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_145])).
% 2.55/1.34  tff(c_40, plain, (![D_51]: (~r2_hidden(D_51, k1_relset_1('#skF_6', '#skF_5', '#skF_7')) | ~m1_subset_1(D_51, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.55/1.34  tff(c_156, plain, (![D_51]: (~r2_hidden(D_51, k1_relat_1('#skF_7')) | ~m1_subset_1(D_51, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_40])).
% 2.55/1.34  tff(c_337, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_329, c_156])).
% 2.55/1.34  tff(c_347, plain, (~m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_120, c_337])).
% 2.55/1.34  tff(c_196, plain, (![A_92, B_93, C_94]: (m1_subset_1(k1_relset_1(A_92, B_93, C_94), k1_zfmisc_1(A_92)) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.34  tff(c_229, plain, (m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_155, c_196])).
% 2.55/1.34  tff(c_245, plain, (m1_subset_1(k1_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_229])).
% 2.55/1.34  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.55/1.34  tff(c_248, plain, (![A_5]: (m1_subset_1(A_5, '#skF_6') | ~r2_hidden(A_5, k1_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_245, c_10])).
% 2.55/1.34  tff(c_333, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6') | k1_relat_1('#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_329, c_248])).
% 2.55/1.34  tff(c_344, plain, (m1_subset_1('#skF_3'(k1_xboole_0, k1_relat_1('#skF_7')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_120, c_333])).
% 2.55/1.34  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_347, c_344])).
% 2.55/1.34  tff(c_352, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(splitRight, [status(thm)], [c_116])).
% 2.55/1.34  tff(c_401, plain, (![A_129, B_130, C_131]: (k2_relset_1(A_129, B_130, C_131)=k2_relat_1(C_131) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.55/1.34  tff(c_404, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_44, c_401])).
% 2.55/1.34  tff(c_412, plain, (k2_relset_1('#skF_6', '#skF_5', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_352, c_404])).
% 2.55/1.34  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_412])).
% 2.55/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.34  
% 2.55/1.34  Inference rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Ref     : 0
% 2.55/1.34  #Sup     : 84
% 2.55/1.34  #Fact    : 0
% 2.55/1.34  #Define  : 0
% 2.55/1.34  #Split   : 2
% 2.55/1.34  #Chain   : 0
% 2.55/1.34  #Close   : 0
% 2.55/1.34  
% 2.55/1.34  Ordering : KBO
% 2.55/1.34  
% 2.55/1.34  Simplification rules
% 2.55/1.34  ----------------------
% 2.55/1.34  #Subsume      : 11
% 2.55/1.34  #Demod        : 22
% 2.55/1.34  #Tautology    : 30
% 2.55/1.34  #SimpNegUnit  : 6
% 2.55/1.34  #BackRed      : 3
% 2.55/1.34  
% 2.55/1.34  #Partial instantiations: 0
% 2.55/1.34  #Strategies tried      : 1
% 2.55/1.34  
% 2.55/1.34  Timing (in seconds)
% 2.55/1.34  ----------------------
% 2.55/1.34  Preprocessing        : 0.32
% 2.55/1.34  Parsing              : 0.17
% 2.55/1.34  CNF conversion       : 0.03
% 2.55/1.34  Main loop            : 0.25
% 2.55/1.34  Inferencing          : 0.09
% 2.55/1.34  Reduction            : 0.07
% 2.55/1.34  Demodulation         : 0.05
% 2.55/1.34  BG Simplification    : 0.01
% 2.55/1.34  Subsumption          : 0.05
% 2.55/1.34  Abstraction          : 0.02
% 2.55/1.34  MUC search           : 0.00
% 2.55/1.34  Cooper               : 0.00
% 2.55/1.34  Total                : 0.60
% 2.55/1.34  Index Insertion      : 0.00
% 2.55/1.34  Index Deletion       : 0.00
% 2.55/1.34  Index Matching       : 0.00
% 2.55/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
