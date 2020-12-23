%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:38 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 130 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   83 ( 241 expanded)
%              Number of equality atoms :   31 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( ~ ( B != k1_xboole_0
              & k7_setfam_1(A,B) = k1_xboole_0 )
          & ~ ( k7_setfam_1(A,B) != k1_xboole_0
              & B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,C)
          <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(c_74,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,
    ( k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_9] : k4_xboole_0('#skF_4',A_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_10])).

tff(c_84,plain,(
    ! [B_38] : k3_xboole_0('#skF_4',B_38) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_55])).

tff(c_110,plain,(
    ! [A_40,B_41,C_42] :
      ( ~ r1_xboole_0(A_40,B_41)
      | ~ r2_hidden(C_42,k3_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [B_38,C_42] :
      ( ~ r1_xboole_0('#skF_4',B_38)
      | ~ r2_hidden(C_42,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_110])).

tff(c_122,plain,(
    ! [C_42] : ~ r2_hidden(C_42,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_16,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ! [A_14] : m1_subset_1('#skF_4',k1_zfmisc_1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_16])).

tff(c_605,plain,(
    ! [A_85,B_86,C_87] :
      ( r2_hidden('#skF_2'(A_85,B_86,C_87),C_87)
      | r2_hidden(k3_subset_1(A_85,'#skF_2'(A_85,B_86,C_87)),B_86)
      | k7_setfam_1(A_85,B_86) = C_87
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k1_zfmisc_1(A_85)))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_623,plain,(
    ! [A_85,C_87] :
      ( r2_hidden('#skF_2'(A_85,'#skF_4',C_87),C_87)
      | k7_setfam_1(A_85,'#skF_4') = C_87
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k1_zfmisc_1(A_85)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_85))) ) ),
    inference(resolution,[status(thm)],[c_605,c_122])).

tff(c_636,plain,(
    ! [A_88,C_89] :
      ( r2_hidden('#skF_2'(A_88,'#skF_4',C_89),C_89)
      | k7_setfam_1(A_88,'#skF_4') = C_89
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_623])).

tff(c_642,plain,(
    ! [A_88] :
      ( r2_hidden('#skF_2'(A_88,'#skF_4','#skF_4'),'#skF_4')
      | k7_setfam_1(A_88,'#skF_4') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_56,c_636])).

tff(c_646,plain,(
    ! [A_88] : k7_setfam_1(A_88,'#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_642])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_4'
    | k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_73,plain,(
    k7_setfam_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_44])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_73])).

tff(c_651,plain,(
    ! [B_38] : ~ r1_xboole_0('#skF_4',B_38) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_6,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6])).

tff(c_807,plain,(
    ! [B_115,C_116,A_117] :
      ( r1_xboole_0(B_115,C_116)
      | ~ r1_tarski(B_115,k3_subset_1(A_117,C_116))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_814,plain,(
    ! [C_116,A_117] :
      ( r1_xboole_0('#skF_4',C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_117))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_57,c_807])).

tff(c_818,plain,(
    ! [C_116,A_117] :
      ( r1_xboole_0('#skF_4',C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_117)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_814])).

tff(c_819,plain,(
    ! [C_116,A_117] : ~ m1_subset_1(C_116,k1_zfmisc_1(A_117)) ),
    inference(negUnitSimplification,[status(thm)],[c_651,c_818])).

tff(c_821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_819,c_56])).

tff(c_823,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_822,plain,(
    k7_setfam_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_929,plain,(
    ! [A_138,B_139] :
      ( k7_setfam_1(A_138,B_139) != k1_xboole_0
      | k1_xboole_0 = B_139
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k1_zfmisc_1(A_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_932,plain,
    ( k7_setfam_1('#skF_3','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_929])).

tff(c_939,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_822,c_932])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.48  
% 2.95/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k7_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.95/1.48  
% 2.95/1.48  %Foreground sorts:
% 2.95/1.48  
% 2.95/1.48  
% 2.95/1.48  %Background operators:
% 2.95/1.48  
% 2.95/1.48  
% 2.95/1.48  %Foreground operators:
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.48  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.95/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.95/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.95/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.48  
% 2.95/1.49  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.95/1.49  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)) & ~(~(k7_setfam_1(A, B) = k1_xboole_0) & (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tops_2)).
% 2.95/1.49  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.95/1.49  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.95/1.49  tff(f_56, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.95/1.49  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.95/1.49  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.95/1.49  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.95/1.49  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.95/1.49  tff(c_74, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.49  tff(c_38, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.49  tff(c_54, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_38])).
% 2.95/1.49  tff(c_10, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.95/1.49  tff(c_55, plain, (![A_9]: (k4_xboole_0('#skF_4', A_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_10])).
% 2.95/1.49  tff(c_84, plain, (![B_38]: (k3_xboole_0('#skF_4', B_38)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_74, c_55])).
% 2.95/1.49  tff(c_110, plain, (![A_40, B_41, C_42]: (~r1_xboole_0(A_40, B_41) | ~r2_hidden(C_42, k3_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.49  tff(c_113, plain, (![B_38, C_42]: (~r1_xboole_0('#skF_4', B_38) | ~r2_hidden(C_42, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_84, c_110])).
% 2.95/1.49  tff(c_122, plain, (![C_42]: (~r2_hidden(C_42, '#skF_4'))), inference(splitLeft, [status(thm)], [c_113])).
% 2.95/1.49  tff(c_16, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.95/1.49  tff(c_56, plain, (![A_14]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_16])).
% 2.95/1.49  tff(c_605, plain, (![A_85, B_86, C_87]: (r2_hidden('#skF_2'(A_85, B_86, C_87), C_87) | r2_hidden(k3_subset_1(A_85, '#skF_2'(A_85, B_86, C_87)), B_86) | k7_setfam_1(A_85, B_86)=C_87 | ~m1_subset_1(C_87, k1_zfmisc_1(k1_zfmisc_1(A_85))) | ~m1_subset_1(B_86, k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.95/1.49  tff(c_623, plain, (![A_85, C_87]: (r2_hidden('#skF_2'(A_85, '#skF_4', C_87), C_87) | k7_setfam_1(A_85, '#skF_4')=C_87 | ~m1_subset_1(C_87, k1_zfmisc_1(k1_zfmisc_1(A_85))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_85))))), inference(resolution, [status(thm)], [c_605, c_122])).
% 2.95/1.49  tff(c_636, plain, (![A_88, C_89]: (r2_hidden('#skF_2'(A_88, '#skF_4', C_89), C_89) | k7_setfam_1(A_88, '#skF_4')=C_89 | ~m1_subset_1(C_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_623])).
% 2.95/1.49  tff(c_642, plain, (![A_88]: (r2_hidden('#skF_2'(A_88, '#skF_4', '#skF_4'), '#skF_4') | k7_setfam_1(A_88, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_56, c_636])).
% 2.95/1.49  tff(c_646, plain, (![A_88]: (k7_setfam_1(A_88, '#skF_4')='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_122, c_642])).
% 2.95/1.49  tff(c_44, plain, (k1_xboole_0!='#skF_4' | k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.49  tff(c_73, plain, (k7_setfam_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_44])).
% 2.95/1.49  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_646, c_73])).
% 2.95/1.49  tff(c_651, plain, (![B_38]: (~r1_xboole_0('#skF_4', B_38))), inference(splitRight, [status(thm)], [c_113])).
% 2.95/1.49  tff(c_6, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.49  tff(c_57, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6])).
% 2.95/1.49  tff(c_807, plain, (![B_115, C_116, A_117]: (r1_xboole_0(B_115, C_116) | ~r1_tarski(B_115, k3_subset_1(A_117, C_116)) | ~m1_subset_1(C_116, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.95/1.49  tff(c_814, plain, (![C_116, A_117]: (r1_xboole_0('#skF_4', C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_117)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_117)))), inference(resolution, [status(thm)], [c_57, c_807])).
% 2.95/1.49  tff(c_818, plain, (![C_116, A_117]: (r1_xboole_0('#skF_4', C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_117)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_814])).
% 2.95/1.49  tff(c_819, plain, (![C_116, A_117]: (~m1_subset_1(C_116, k1_zfmisc_1(A_117)))), inference(negUnitSimplification, [status(thm)], [c_651, c_818])).
% 2.95/1.49  tff(c_821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_819, c_56])).
% 2.95/1.49  tff(c_823, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.95/1.49  tff(c_822, plain, (k7_setfam_1('#skF_3', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.95/1.49  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.95/1.49  tff(c_929, plain, (![A_138, B_139]: (k7_setfam_1(A_138, B_139)!=k1_xboole_0 | k1_xboole_0=B_139 | ~m1_subset_1(B_139, k1_zfmisc_1(k1_zfmisc_1(A_138))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.95/1.49  tff(c_932, plain, (k7_setfam_1('#skF_3', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_929])).
% 2.95/1.49  tff(c_939, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_822, c_932])).
% 2.95/1.49  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_823, c_939])).
% 2.95/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.49  
% 2.95/1.49  Inference rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Ref     : 0
% 2.95/1.49  #Sup     : 200
% 2.95/1.49  #Fact    : 0
% 2.95/1.49  #Define  : 0
% 2.95/1.49  #Split   : 3
% 2.95/1.49  #Chain   : 0
% 2.95/1.49  #Close   : 0
% 2.95/1.49  
% 2.95/1.49  Ordering : KBO
% 2.95/1.49  
% 2.95/1.49  Simplification rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Subsume      : 7
% 2.95/1.49  #Demod        : 251
% 2.95/1.49  #Tautology    : 144
% 2.95/1.49  #SimpNegUnit  : 7
% 2.95/1.49  #BackRed      : 6
% 2.95/1.49  
% 2.95/1.49  #Partial instantiations: 0
% 2.95/1.49  #Strategies tried      : 1
% 2.95/1.49  
% 2.95/1.49  Timing (in seconds)
% 2.95/1.49  ----------------------
% 3.10/1.50  Preprocessing        : 0.36
% 3.10/1.50  Parsing              : 0.18
% 3.10/1.50  CNF conversion       : 0.03
% 3.10/1.50  Main loop            : 0.36
% 3.10/1.50  Inferencing          : 0.13
% 3.10/1.50  Reduction            : 0.13
% 3.10/1.50  Demodulation         : 0.10
% 3.10/1.50  BG Simplification    : 0.02
% 3.10/1.50  Subsumption          : 0.05
% 3.10/1.50  Abstraction          : 0.02
% 3.10/1.50  MUC search           : 0.00
% 3.10/1.50  Cooper               : 0.00
% 3.10/1.50  Total                : 0.74
% 3.10/1.50  Index Insertion      : 0.00
% 3.10/1.50  Index Deletion       : 0.00
% 3.10/1.50  Index Matching       : 0.00
% 3.10/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
