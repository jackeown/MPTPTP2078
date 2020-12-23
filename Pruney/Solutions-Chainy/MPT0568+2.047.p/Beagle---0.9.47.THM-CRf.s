%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:26 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   59 (  80 expanded)
%              Number of leaves         :   42 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  75 expanded)
%              Number of equality atoms :   15 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_20 > #skF_17 > #skF_12 > #skF_3 > #skF_8 > #skF_14 > #skF_18 > #skF_19 > #skF_7 > #skF_11 > #skF_9 > #skF_13 > #skF_2 > #skF_1 > #skF_16 > #skF_5 > #skF_15 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_18',type,(
    '#skF_18': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_19',type,(
    '#skF_19': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_16',type,(
    '#skF_16': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_119,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_726,plain,(
    ! [A_205,B_206] :
      ( r2_hidden(k4_tarski('#skF_16'(A_205,B_206),'#skF_17'(A_205,B_206)),A_205)
      | r2_hidden('#skF_18'(A_205,B_206),B_206)
      | k1_relat_1(A_205) = B_206 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_125,plain,(
    ! [B_134,A_135] :
      ( ~ r2_hidden(B_134,A_135)
      | k4_xboole_0(A_135,k1_tarski(B_134)) != A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_130,plain,(
    ! [B_134] : ~ r2_hidden(B_134,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_125])).

tff(c_800,plain,(
    ! [B_208] :
      ( r2_hidden('#skF_18'(k1_xboole_0,B_208),B_208)
      | k1_relat_1(k1_xboole_0) = B_208 ) ),
    inference(resolution,[status(thm)],[c_726,c_130])).

tff(c_869,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_800,c_130])).

tff(c_798,plain,(
    ! [B_206] :
      ( r2_hidden('#skF_18'(k1_xboole_0,B_206),B_206)
      | k1_relat_1(k1_xboole_0) = B_206 ) ),
    inference(resolution,[status(thm)],[c_726,c_130])).

tff(c_1233,plain,(
    ! [B_227] :
      ( r2_hidden('#skF_18'(k1_xboole_0,B_227),B_227)
      | k1_xboole_0 = B_227 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_798])).

tff(c_76,plain,(
    ! [A_80] :
      ( r2_hidden('#skF_13'(A_80),A_80)
      | v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_131,plain,(
    ! [B_136] : ~ r2_hidden(B_136,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_125])).

tff(c_136,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_76,c_131])).

tff(c_1016,plain,(
    ! [D_214,A_215,B_216] :
      ( r2_hidden(k4_tarski(D_214,'#skF_12'(A_215,B_216,k10_relat_1(A_215,B_216),D_214)),A_215)
      | ~ r2_hidden(D_214,k10_relat_1(A_215,B_216))
      | ~ v1_relat_1(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1033,plain,(
    ! [D_214,B_216] :
      ( ~ r2_hidden(D_214,k10_relat_1(k1_xboole_0,B_216))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1016,c_130])).

tff(c_1043,plain,(
    ! [D_214,B_216] : ~ r2_hidden(D_214,k10_relat_1(k1_xboole_0,B_216)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_1033])).

tff(c_1257,plain,(
    ! [B_216] : k10_relat_1(k1_xboole_0,B_216) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1233,c_1043])).

tff(c_96,plain,(
    k10_relat_1(k1_xboole_0,'#skF_20') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1257,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:45:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.49  
% 3.27/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_20 > #skF_17 > #skF_12 > #skF_3 > #skF_8 > #skF_14 > #skF_18 > #skF_19 > #skF_7 > #skF_11 > #skF_9 > #skF_13 > #skF_2 > #skF_1 > #skF_16 > #skF_5 > #skF_15 > #skF_4 > #skF_10
% 3.27/1.50  
% 3.27/1.50  %Foreground sorts:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Background operators:
% 3.27/1.50  
% 3.27/1.50  
% 3.27/1.50  %Foreground operators:
% 3.27/1.50  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_20', type, '#skF_20': $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.27/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.27/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.27/1.50  tff('#skF_17', type, '#skF_17': ($i * $i) > $i).
% 3.27/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.50  tff('#skF_12', type, '#skF_12': ($i * $i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.27/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.50  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_18', type, '#skF_18': ($i * $i) > $i).
% 3.27/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.27/1.50  tff('#skF_19', type, '#skF_19': ($i * $i * $i) > $i).
% 3.27/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.27/1.50  tff('#skF_13', type, '#skF_13': $i > $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.50  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.27/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_16', type, '#skF_16': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.27/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.50  tff('#skF_15', type, '#skF_15': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.27/1.50  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 3.27/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.50  
% 3.27/1.51  tff(f_108, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 3.27/1.51  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.27/1.51  tff(f_63, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.27/1.51  tff(f_100, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 3.27/1.51  tff(f_90, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 3.27/1.51  tff(f_119, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 3.27/1.51  tff(c_726, plain, (![A_205, B_206]: (r2_hidden(k4_tarski('#skF_16'(A_205, B_206), '#skF_17'(A_205, B_206)), A_205) | r2_hidden('#skF_18'(A_205, B_206), B_206) | k1_relat_1(A_205)=B_206)), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.27/1.51  tff(c_6, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.27/1.51  tff(c_125, plain, (![B_134, A_135]: (~r2_hidden(B_134, A_135) | k4_xboole_0(A_135, k1_tarski(B_134))!=A_135)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.27/1.51  tff(c_130, plain, (![B_134]: (~r2_hidden(B_134, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_125])).
% 3.27/1.51  tff(c_800, plain, (![B_208]: (r2_hidden('#skF_18'(k1_xboole_0, B_208), B_208) | k1_relat_1(k1_xboole_0)=B_208)), inference(resolution, [status(thm)], [c_726, c_130])).
% 3.27/1.51  tff(c_869, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_800, c_130])).
% 3.27/1.51  tff(c_798, plain, (![B_206]: (r2_hidden('#skF_18'(k1_xboole_0, B_206), B_206) | k1_relat_1(k1_xboole_0)=B_206)), inference(resolution, [status(thm)], [c_726, c_130])).
% 3.27/1.51  tff(c_1233, plain, (![B_227]: (r2_hidden('#skF_18'(k1_xboole_0, B_227), B_227) | k1_xboole_0=B_227)), inference(demodulation, [status(thm), theory('equality')], [c_869, c_798])).
% 3.27/1.51  tff(c_76, plain, (![A_80]: (r2_hidden('#skF_13'(A_80), A_80) | v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.27/1.51  tff(c_131, plain, (![B_136]: (~r2_hidden(B_136, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_125])).
% 3.27/1.51  tff(c_136, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_131])).
% 3.27/1.51  tff(c_1016, plain, (![D_214, A_215, B_216]: (r2_hidden(k4_tarski(D_214, '#skF_12'(A_215, B_216, k10_relat_1(A_215, B_216), D_214)), A_215) | ~r2_hidden(D_214, k10_relat_1(A_215, B_216)) | ~v1_relat_1(A_215))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.27/1.51  tff(c_1033, plain, (![D_214, B_216]: (~r2_hidden(D_214, k10_relat_1(k1_xboole_0, B_216)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1016, c_130])).
% 3.27/1.51  tff(c_1043, plain, (![D_214, B_216]: (~r2_hidden(D_214, k10_relat_1(k1_xboole_0, B_216)))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_1033])).
% 3.27/1.51  tff(c_1257, plain, (![B_216]: (k10_relat_1(k1_xboole_0, B_216)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1233, c_1043])).
% 3.27/1.51  tff(c_96, plain, (k10_relat_1(k1_xboole_0, '#skF_20')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.27/1.51  tff(c_1274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1257, c_96])).
% 3.27/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.51  
% 3.27/1.51  Inference rules
% 3.27/1.51  ----------------------
% 3.27/1.51  #Ref     : 1
% 3.27/1.51  #Sup     : 224
% 3.27/1.51  #Fact    : 0
% 3.27/1.51  #Define  : 0
% 3.27/1.51  #Split   : 0
% 3.27/1.51  #Chain   : 0
% 3.27/1.51  #Close   : 0
% 3.27/1.51  
% 3.27/1.51  Ordering : KBO
% 3.27/1.51  
% 3.27/1.51  Simplification rules
% 3.27/1.51  ----------------------
% 3.27/1.51  #Subsume      : 42
% 3.27/1.51  #Demod        : 222
% 3.27/1.51  #Tautology    : 86
% 3.27/1.51  #SimpNegUnit  : 8
% 3.27/1.51  #BackRed      : 33
% 3.27/1.51  
% 3.27/1.51  #Partial instantiations: 0
% 3.27/1.51  #Strategies tried      : 1
% 3.27/1.51  
% 3.27/1.51  Timing (in seconds)
% 3.27/1.51  ----------------------
% 3.42/1.51  Preprocessing        : 0.32
% 3.42/1.51  Parsing              : 0.16
% 3.42/1.51  CNF conversion       : 0.03
% 3.42/1.51  Main loop            : 0.40
% 3.42/1.51  Inferencing          : 0.14
% 3.42/1.51  Reduction            : 0.12
% 3.42/1.51  Demodulation         : 0.07
% 3.42/1.51  BG Simplification    : 0.03
% 3.42/1.51  Subsumption          : 0.09
% 3.42/1.51  Abstraction          : 0.02
% 3.42/1.51  MUC search           : 0.00
% 3.42/1.51  Cooper               : 0.00
% 3.42/1.51  Total                : 0.74
% 3.42/1.51  Index Insertion      : 0.00
% 3.42/1.51  Index Deletion       : 0.00
% 3.42/1.51  Index Matching       : 0.00
% 3.42/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
