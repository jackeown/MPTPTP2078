%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:27 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   38 (  57 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 224 expanded)
%              Number of equality atoms :   30 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_57,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_42,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_250,plain,(
    ! [D_100,C_101,B_102,A_103] :
      ( r2_hidden(k1_funct_1(D_100,C_101),B_102)
      | k1_xboole_0 = B_102
      | ~ r2_hidden(C_101,A_103)
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102)))
      | ~ v1_funct_2(D_100,A_103,B_102)
      | ~ v1_funct_1(D_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_263,plain,(
    ! [D_104,B_105] :
      ( r2_hidden(k1_funct_1(D_104,'#skF_5'),B_105)
      | k1_xboole_0 = B_105
      | ~ m1_subset_1(D_104,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_105)))
      | ~ v1_funct_2(D_104,'#skF_3',B_105)
      | ~ v1_funct_1(D_104) ) ),
    inference(resolution,[status(thm)],[c_44,c_250])).

tff(c_266,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_263])).

tff(c_269,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_266])).

tff(c_270,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_36,plain,(
    ! [A_39] : k1_setfam_1(k1_tarski(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_95,plain,(
    ! [A_55,B_56] : k1_setfam_1(k2_tarski(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = k1_setfam_1(k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_107,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_104])).

tff(c_117,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_145,plain,(
    ! [A_62] : k5_xboole_0(A_62,A_62) = k4_xboole_0(A_62,A_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_117])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_4])).

tff(c_32,plain,(
    ! [B_38] : k4_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) != k1_tarski(B_38) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_291,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_32])).

tff(c_312,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_152,c_270,c_291])).

tff(c_313,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_6,plain,(
    ! [C_8,A_4] :
      ( C_8 = A_4
      | ~ r2_hidden(C_8,k1_tarski(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_320,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_313,c_6])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.33  
% 2.27/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.27/1.34  
% 2.27/1.34  %Foreground sorts:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Background operators:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Foreground operators:
% 2.27/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.27/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.27/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.27/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.27/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.27/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.27/1.34  
% 2.27/1.35  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.27/1.35  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.27/1.35  tff(f_57, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.27/1.35  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.35  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.27/1.35  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.27/1.35  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.27/1.35  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.27/1.35  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.27/1.35  tff(c_42, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.35  tff(c_50, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.35  tff(c_48, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.35  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.35  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.35  tff(c_250, plain, (![D_100, C_101, B_102, A_103]: (r2_hidden(k1_funct_1(D_100, C_101), B_102) | k1_xboole_0=B_102 | ~r2_hidden(C_101, A_103) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))) | ~v1_funct_2(D_100, A_103, B_102) | ~v1_funct_1(D_100))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.27/1.35  tff(c_263, plain, (![D_104, B_105]: (r2_hidden(k1_funct_1(D_104, '#skF_5'), B_105) | k1_xboole_0=B_105 | ~m1_subset_1(D_104, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_105))) | ~v1_funct_2(D_104, '#skF_3', B_105) | ~v1_funct_1(D_104))), inference(resolution, [status(thm)], [c_44, c_250])).
% 2.27/1.35  tff(c_266, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_263])).
% 2.27/1.35  tff(c_269, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_266])).
% 2.27/1.35  tff(c_270, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_269])).
% 2.27/1.35  tff(c_36, plain, (![A_39]: (k1_setfam_1(k1_tarski(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.35  tff(c_18, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.27/1.35  tff(c_95, plain, (![A_55, B_56]: (k1_setfam_1(k2_tarski(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.27/1.35  tff(c_104, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=k1_setfam_1(k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 2.27/1.35  tff(c_107, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_104])).
% 2.27/1.35  tff(c_117, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.35  tff(c_145, plain, (![A_62]: (k5_xboole_0(A_62, A_62)=k4_xboole_0(A_62, A_62))), inference(superposition, [status(thm), theory('equality')], [c_107, c_117])).
% 2.27/1.35  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.35  tff(c_152, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_145, c_4])).
% 2.27/1.35  tff(c_32, plain, (![B_38]: (k4_xboole_0(k1_tarski(B_38), k1_tarski(B_38))!=k1_tarski(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.27/1.35  tff(c_291, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_270, c_32])).
% 2.27/1.35  tff(c_312, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_152, c_270, c_291])).
% 2.27/1.35  tff(c_313, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_269])).
% 2.27/1.35  tff(c_6, plain, (![C_8, A_4]: (C_8=A_4 | ~r2_hidden(C_8, k1_tarski(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.27/1.35  tff(c_320, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_313, c_6])).
% 2.27/1.35  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_320])).
% 2.27/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  Inference rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Ref     : 0
% 2.27/1.35  #Sup     : 62
% 2.27/1.35  #Fact    : 0
% 2.27/1.35  #Define  : 0
% 2.27/1.35  #Split   : 1
% 2.27/1.35  #Chain   : 0
% 2.27/1.35  #Close   : 0
% 2.27/1.35  
% 2.27/1.35  Ordering : KBO
% 2.27/1.35  
% 2.27/1.35  Simplification rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Subsume      : 0
% 2.27/1.35  #Demod        : 20
% 2.27/1.35  #Tautology    : 39
% 2.27/1.35  #SimpNegUnit  : 1
% 2.27/1.35  #BackRed      : 2
% 2.27/1.35  
% 2.27/1.35  #Partial instantiations: 0
% 2.27/1.35  #Strategies tried      : 1
% 2.27/1.35  
% 2.27/1.35  Timing (in seconds)
% 2.27/1.35  ----------------------
% 2.27/1.35  Preprocessing        : 0.33
% 2.27/1.35  Parsing              : 0.18
% 2.27/1.35  CNF conversion       : 0.02
% 2.27/1.35  Main loop            : 0.20
% 2.27/1.35  Inferencing          : 0.08
% 2.27/1.35  Reduction            : 0.06
% 2.27/1.35  Demodulation         : 0.04
% 2.27/1.35  BG Simplification    : 0.02
% 2.27/1.35  Subsumption          : 0.04
% 2.27/1.35  Abstraction          : 0.02
% 2.27/1.35  MUC search           : 0.00
% 2.27/1.35  Cooper               : 0.00
% 2.27/1.35  Total                : 0.56
% 2.27/1.35  Index Insertion      : 0.00
% 2.27/1.35  Index Deletion       : 0.00
% 2.27/1.35  Index Matching       : 0.00
% 2.27/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
