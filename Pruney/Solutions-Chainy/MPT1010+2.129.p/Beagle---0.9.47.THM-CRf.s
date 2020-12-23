%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:22 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   57 (  65 expanded)
%              Number of leaves         :   33 (  39 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 101 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_46,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : k4_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k3_xboole_0(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_149,plain,(
    ! [A_2] : k4_xboole_0(A_2,A_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_38,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    ! [B_19] : k1_tarski(B_19) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_38])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_840,plain,(
    ! [D_109,C_110,B_111,A_112] :
      ( r2_hidden(k1_funct_1(D_109,C_110),B_111)
      | k1_xboole_0 = B_111
      | ~ r2_hidden(C_110,A_112)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111)))
      | ~ v1_funct_2(D_109,A_112,B_111)
      | ~ v1_funct_1(D_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_865,plain,(
    ! [D_113,B_114] :
      ( r2_hidden(k1_funct_1(D_113,'#skF_5'),B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_114)))
      | ~ v1_funct_2(D_113,'#skF_3',B_114)
      | ~ v1_funct_1(D_113) ) ),
    inference(resolution,[status(thm)],[c_48,c_840])).

tff(c_868,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_865])).

tff(c_871,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_868])).

tff(c_872,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_871])).

tff(c_32,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_296,plain,(
    ! [E_64,C_65,B_66,A_67] :
      ( E_64 = C_65
      | E_64 = B_66
      | E_64 = A_67
      | ~ r2_hidden(E_64,k1_enumset1(A_67,B_66,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_315,plain,(
    ! [E_68,B_69,A_70] :
      ( E_68 = B_69
      | E_68 = A_70
      | E_68 = A_70
      | ~ r2_hidden(E_68,k2_tarski(A_70,B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_296])).

tff(c_324,plain,(
    ! [E_68,A_12] :
      ( E_68 = A_12
      | E_68 = A_12
      | E_68 = A_12
      | ~ r2_hidden(E_68,k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_315])).

tff(c_877,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_872,c_324])).

tff(c_882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_46,c_877])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:05:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.67  
% 3.22/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.67  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 3.22/1.67  
% 3.22/1.67  %Foreground sorts:
% 3.22/1.67  
% 3.22/1.67  
% 3.22/1.67  %Background operators:
% 3.22/1.67  
% 3.22/1.67  
% 3.22/1.67  %Foreground operators:
% 3.22/1.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.22/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.22/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.22/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.22/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.67  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.22/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.22/1.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.67  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.22/1.67  
% 3.22/1.68  tff(f_82, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.22/1.68  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.22/1.68  tff(f_29, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.22/1.68  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.22/1.68  tff(f_57, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 3.22/1.68  tff(f_71, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.22/1.68  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.22/1.68  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.22/1.68  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.22/1.68  tff(c_46, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.68  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.22/1.68  tff(c_4, plain, (![A_2]: (k4_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.22/1.68  tff(c_131, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.22/1.68  tff(c_146, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k3_xboole_0(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_131])).
% 3.22/1.68  tff(c_149, plain, (![A_2]: (k4_xboole_0(A_2, A_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_146])).
% 3.22/1.68  tff(c_38, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.22/1.68  tff(c_150, plain, (![B_19]: (k1_tarski(B_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_38])).
% 3.22/1.68  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.68  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.68  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.68  tff(c_48, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.22/1.68  tff(c_840, plain, (![D_109, C_110, B_111, A_112]: (r2_hidden(k1_funct_1(D_109, C_110), B_111) | k1_xboole_0=B_111 | ~r2_hidden(C_110, A_112) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))) | ~v1_funct_2(D_109, A_112, B_111) | ~v1_funct_1(D_109))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.22/1.68  tff(c_865, plain, (![D_113, B_114]: (r2_hidden(k1_funct_1(D_113, '#skF_5'), B_114) | k1_xboole_0=B_114 | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_114))) | ~v1_funct_2(D_113, '#skF_3', B_114) | ~v1_funct_1(D_113))), inference(resolution, [status(thm)], [c_48, c_840])).
% 3.22/1.68  tff(c_868, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_865])).
% 3.22/1.68  tff(c_871, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_868])).
% 3.22/1.68  tff(c_872, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_150, c_871])).
% 3.22/1.68  tff(c_32, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.22/1.68  tff(c_34, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.22/1.68  tff(c_296, plain, (![E_64, C_65, B_66, A_67]: (E_64=C_65 | E_64=B_66 | E_64=A_67 | ~r2_hidden(E_64, k1_enumset1(A_67, B_66, C_65)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.22/1.68  tff(c_315, plain, (![E_68, B_69, A_70]: (E_68=B_69 | E_68=A_70 | E_68=A_70 | ~r2_hidden(E_68, k2_tarski(A_70, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_296])).
% 3.22/1.68  tff(c_324, plain, (![E_68, A_12]: (E_68=A_12 | E_68=A_12 | E_68=A_12 | ~r2_hidden(E_68, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_315])).
% 3.22/1.68  tff(c_877, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_872, c_324])).
% 3.22/1.68  tff(c_882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_46, c_877])).
% 3.22/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.68  
% 3.22/1.68  Inference rules
% 3.22/1.68  ----------------------
% 3.22/1.68  #Ref     : 0
% 3.22/1.68  #Sup     : 189
% 3.22/1.68  #Fact    : 0
% 3.22/1.68  #Define  : 0
% 3.22/1.68  #Split   : 0
% 3.22/1.68  #Chain   : 0
% 3.22/1.68  #Close   : 0
% 3.22/1.68  
% 3.22/1.68  Ordering : KBO
% 3.22/1.68  
% 3.22/1.68  Simplification rules
% 3.22/1.68  ----------------------
% 3.22/1.68  #Subsume      : 19
% 3.22/1.68  #Demod        : 232
% 3.22/1.68  #Tautology    : 112
% 3.22/1.68  #SimpNegUnit  : 12
% 3.22/1.68  #BackRed      : 2
% 3.22/1.68  
% 3.22/1.68  #Partial instantiations: 0
% 3.22/1.68  #Strategies tried      : 1
% 3.22/1.68  
% 3.22/1.68  Timing (in seconds)
% 3.22/1.68  ----------------------
% 3.22/1.69  Preprocessing        : 0.45
% 3.22/1.69  Parsing              : 0.21
% 3.22/1.69  CNF conversion       : 0.04
% 3.22/1.69  Main loop            : 0.42
% 3.22/1.69  Inferencing          : 0.16
% 3.22/1.70  Reduction            : 0.16
% 3.22/1.70  Demodulation         : 0.12
% 3.22/1.70  BG Simplification    : 0.03
% 3.22/1.70  Subsumption          : 0.06
% 3.22/1.70  Abstraction          : 0.03
% 3.22/1.70  MUC search           : 0.00
% 3.22/1.70  Cooper               : 0.00
% 3.22/1.70  Total                : 0.90
% 3.22/1.70  Index Insertion      : 0.00
% 3.22/1.70  Index Deletion       : 0.00
% 3.22/1.70  Index Matching       : 0.00
% 3.22/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
