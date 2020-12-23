%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   58 (  96 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 159 expanded)
%              Number of equality atoms :   12 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_199,plain,(
    ! [A_54,C_55,B_56] :
      ( m1_subset_1(A_54,C_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(C_55))
      | ~ r2_hidden(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_212,plain,(
    ! [A_57] :
      ( m1_subset_1(A_57,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_57,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_199])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(A_24,B_25)
      | ~ m1_subset_1(A_24,k1_zfmisc_1(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_223,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,'#skF_3')
      | ~ r2_hidden(A_58,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_212,c_34])).

tff(c_228,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_223])).

tff(c_229,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_236,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_229,c_8])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_236])).

tff(c_243,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_209,plain,(
    ! [A_54] :
      ( m1_subset_1(A_54,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_54,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_199])).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [C_45,B_46,A_47] :
      ( ~ v1_xboole_0(C_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(C_45))
      | ~ r2_hidden(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_121,plain,(
    ! [A_8,A_47] :
      ( ~ v1_xboole_0(A_8)
      | ~ r2_hidden(A_47,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_109])).

tff(c_122,plain,(
    ! [A_47] : ~ r2_hidden(A_47,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_42,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_256,plain,(
    ! [A_61,B_62] :
      ( k7_setfam_1(A_61,k7_setfam_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_261,plain,(
    k7_setfam_1('#skF_3',k7_setfam_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_256])).

tff(c_270,plain,(
    k7_setfam_1('#skF_3',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_261])).

tff(c_475,plain,(
    ! [A_89,D_90,B_91] :
      ( r2_hidden(k3_subset_1(A_89,D_90),B_91)
      | ~ r2_hidden(D_90,k7_setfam_1(A_89,B_91))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(A_89))
      | ~ m1_subset_1(k7_setfam_1(A_89,B_91),k1_zfmisc_1(k1_zfmisc_1(A_89)))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(A_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_483,plain,(
    ! [D_90] :
      ( r2_hidden(k3_subset_1('#skF_3',D_90),k1_xboole_0)
      | ~ r2_hidden(D_90,k7_setfam_1('#skF_3',k1_xboole_0))
      | ~ m1_subset_1(D_90,k1_zfmisc_1('#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_475])).

tff(c_495,plain,(
    ! [D_90] :
      ( r2_hidden(k3_subset_1('#skF_3',D_90),k1_xboole_0)
      | ~ r2_hidden(D_90,'#skF_4')
      | ~ m1_subset_1(D_90,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46,c_270,c_483])).

tff(c_537,plain,(
    ! [D_92] :
      ( ~ r2_hidden(D_92,'#skF_4')
      | ~ m1_subset_1(D_92,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_495])).

tff(c_572,plain,(
    ! [A_93] : ~ r2_hidden(A_93,'#skF_4') ),
    inference(resolution,[status(thm)],[c_209,c_537])).

tff(c_576,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_572])).

tff(c_580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_576])).

tff(c_581,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_581,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  
% 2.60/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.60/1.41  
% 2.60/1.41  %Foreground sorts:
% 2.60/1.41  
% 2.60/1.41  
% 2.60/1.41  %Background operators:
% 2.60/1.41  
% 2.60/1.41  
% 2.60/1.41  %Foreground operators:
% 2.60/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.60/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.60/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.41  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.60/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.60/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.60/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.60/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.60/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.60/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.60/1.41  
% 2.60/1.42  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.60/1.42  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.60/1.42  tff(f_76, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.60/1.42  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.60/1.42  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.60/1.42  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.60/1.42  tff(f_83, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.60/1.42  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.60/1.42  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.60/1.42  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.60/1.42  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.60/1.42  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.42  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.60/1.42  tff(c_199, plain, (![A_54, C_55, B_56]: (m1_subset_1(A_54, C_55) | ~m1_subset_1(B_56, k1_zfmisc_1(C_55)) | ~r2_hidden(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.60/1.42  tff(c_212, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_57, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_199])).
% 2.60/1.42  tff(c_34, plain, (![A_24, B_25]: (r1_tarski(A_24, B_25) | ~m1_subset_1(A_24, k1_zfmisc_1(B_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.42  tff(c_223, plain, (![A_58]: (r1_tarski(A_58, '#skF_3') | ~r2_hidden(A_58, '#skF_4'))), inference(resolution, [status(thm)], [c_212, c_34])).
% 2.60/1.42  tff(c_228, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_223])).
% 2.60/1.42  tff(c_229, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_228])).
% 2.60/1.42  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.60/1.42  tff(c_236, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_229, c_8])).
% 2.60/1.42  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_236])).
% 2.60/1.42  tff(c_243, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_228])).
% 2.60/1.42  tff(c_209, plain, (![A_54]: (m1_subset_1(A_54, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_54, '#skF_4'))), inference(resolution, [status(thm)], [c_46, c_199])).
% 2.60/1.42  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.60/1.42  tff(c_109, plain, (![C_45, B_46, A_47]: (~v1_xboole_0(C_45) | ~m1_subset_1(B_46, k1_zfmisc_1(C_45)) | ~r2_hidden(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.60/1.42  tff(c_121, plain, (![A_8, A_47]: (~v1_xboole_0(A_8) | ~r2_hidden(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_109])).
% 2.60/1.42  tff(c_122, plain, (![A_47]: (~r2_hidden(A_47, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_121])).
% 2.60/1.42  tff(c_42, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.60/1.42  tff(c_256, plain, (![A_61, B_62]: (k7_setfam_1(A_61, k7_setfam_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.60/1.42  tff(c_261, plain, (k7_setfam_1('#skF_3', k7_setfam_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_256])).
% 2.60/1.42  tff(c_270, plain, (k7_setfam_1('#skF_3', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_261])).
% 2.60/1.42  tff(c_475, plain, (![A_89, D_90, B_91]: (r2_hidden(k3_subset_1(A_89, D_90), B_91) | ~r2_hidden(D_90, k7_setfam_1(A_89, B_91)) | ~m1_subset_1(D_90, k1_zfmisc_1(A_89)) | ~m1_subset_1(k7_setfam_1(A_89, B_91), k1_zfmisc_1(k1_zfmisc_1(A_89))) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(A_89))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.60/1.42  tff(c_483, plain, (![D_90]: (r2_hidden(k3_subset_1('#skF_3', D_90), k1_xboole_0) | ~r2_hidden(D_90, k7_setfam_1('#skF_3', k1_xboole_0)) | ~m1_subset_1(D_90, k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_270, c_475])).
% 2.60/1.42  tff(c_495, plain, (![D_90]: (r2_hidden(k3_subset_1('#skF_3', D_90), k1_xboole_0) | ~r2_hidden(D_90, '#skF_4') | ~m1_subset_1(D_90, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46, c_270, c_483])).
% 2.60/1.42  tff(c_537, plain, (![D_92]: (~r2_hidden(D_92, '#skF_4') | ~m1_subset_1(D_92, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_122, c_495])).
% 2.60/1.42  tff(c_572, plain, (![A_93]: (~r2_hidden(A_93, '#skF_4'))), inference(resolution, [status(thm)], [c_209, c_537])).
% 2.60/1.42  tff(c_576, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_572])).
% 2.60/1.42  tff(c_580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_243, c_576])).
% 2.60/1.42  tff(c_581, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_121])).
% 2.60/1.42  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.60/1.42  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_581, c_6])).
% 2.60/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.42  
% 2.60/1.42  Inference rules
% 2.60/1.42  ----------------------
% 2.60/1.42  #Ref     : 0
% 2.60/1.42  #Sup     : 122
% 2.60/1.42  #Fact    : 0
% 2.60/1.42  #Define  : 0
% 2.60/1.42  #Split   : 6
% 2.60/1.42  #Chain   : 0
% 2.60/1.42  #Close   : 0
% 2.60/1.42  
% 2.60/1.42  Ordering : KBO
% 2.60/1.42  
% 2.60/1.42  Simplification rules
% 2.60/1.42  ----------------------
% 2.60/1.42  #Subsume      : 20
% 2.60/1.42  #Demod        : 52
% 2.60/1.43  #Tautology    : 50
% 2.60/1.43  #SimpNegUnit  : 6
% 2.60/1.43  #BackRed      : 3
% 2.60/1.43  
% 2.60/1.43  #Partial instantiations: 0
% 2.60/1.43  #Strategies tried      : 1
% 2.60/1.43  
% 2.60/1.43  Timing (in seconds)
% 2.60/1.43  ----------------------
% 2.60/1.43  Preprocessing        : 0.33
% 2.60/1.43  Parsing              : 0.18
% 2.60/1.43  CNF conversion       : 0.02
% 2.60/1.43  Main loop            : 0.27
% 2.60/1.43  Inferencing          : 0.10
% 2.60/1.43  Reduction            : 0.08
% 2.60/1.43  Demodulation         : 0.06
% 2.60/1.43  BG Simplification    : 0.02
% 2.60/1.43  Subsumption          : 0.06
% 2.60/1.43  Abstraction          : 0.01
% 2.60/1.43  MUC search           : 0.00
% 2.60/1.43  Cooper               : 0.00
% 2.60/1.43  Total                : 0.62
% 2.60/1.43  Index Insertion      : 0.00
% 2.60/1.43  Index Deletion       : 0.00
% 2.60/1.43  Index Matching       : 0.00
% 2.60/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
