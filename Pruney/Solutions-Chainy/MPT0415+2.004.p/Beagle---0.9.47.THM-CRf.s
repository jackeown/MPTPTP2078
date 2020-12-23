%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   52 (  76 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 124 expanded)
%              Number of equality atoms :   13 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ~ ( B != k1_xboole_0
          & ! [C] :
              ( m1_subset_1(C,A)
             => ~ r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_60,axiom,(
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

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_125,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51),B_51)
      | k1_xboole_0 = B_51
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_141,plain,(
    ! [B_52,A_53] :
      ( ~ v1_xboole_0(B_52)
      | k1_xboole_0 = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_125,c_2])).

tff(c_151,plain,
    ( ~ v1_xboole_0('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_141])).

tff(c_159,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_151])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_38,C_39,B_40] :
      ( m1_subset_1(A_38,C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_73,plain,(
    ! [A_38] :
      ( m1_subset_1(A_38,k1_zfmisc_1('#skF_4'))
      | ~ r2_hidden(A_38,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [C_34,B_35,A_36] :
      ( ~ v1_xboole_0(C_34)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_58,plain,(
    ! [A_8,A_36] :
      ( ~ v1_xboole_0(A_8)
      | ~ r2_hidden(A_36,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_52])).

tff(c_59,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_36,plain,(
    k7_setfam_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_97,plain,(
    ! [A_47,B_48] :
      ( k7_setfam_1(A_47,k7_setfam_1(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_102,plain,(
    k7_setfam_1('#skF_4',k7_setfam_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_40,c_97])).

tff(c_108,plain,(
    k7_setfam_1('#skF_4',k1_xboole_0) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_102])).

tff(c_433,plain,(
    ! [A_91,D_92,B_93] :
      ( r2_hidden(k3_subset_1(A_91,D_92),B_93)
      | ~ r2_hidden(D_92,k7_setfam_1(A_91,B_93))
      | ~ m1_subset_1(D_92,k1_zfmisc_1(A_91))
      | ~ m1_subset_1(k7_setfam_1(A_91,B_93),k1_zfmisc_1(k1_zfmisc_1(A_91)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_439,plain,(
    ! [D_92] :
      ( r2_hidden(k3_subset_1('#skF_4',D_92),k1_xboole_0)
      | ~ r2_hidden(D_92,k7_setfam_1('#skF_4',k1_xboole_0))
      | ~ m1_subset_1(D_92,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_4')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_433])).

tff(c_446,plain,(
    ! [D_92] :
      ( r2_hidden(k3_subset_1('#skF_4',D_92),k1_xboole_0)
      | ~ r2_hidden(D_92,'#skF_5')
      | ~ m1_subset_1(D_92,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_40,c_108,c_439])).

tff(c_450,plain,(
    ! [D_94] :
      ( ~ r2_hidden(D_94,'#skF_5')
      | ~ m1_subset_1(D_94,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_446])).

tff(c_470,plain,(
    ! [A_95] : ~ r2_hidden(A_95,'#skF_5') ),
    inference(resolution,[status(thm)],[c_73,c_450])).

tff(c_478,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_470])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_159,c_478])).

tff(c_486,plain,(
    ! [A_8] : ~ v1_xboole_0(A_8) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.34  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 2.36/1.34  
% 2.36/1.34  %Foreground sorts:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Background operators:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Foreground operators:
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.34  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.36/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.36/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.34  
% 2.36/1.35  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.36/1.35  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ~(~(B = k1_xboole_0) & (![C]: (m1_subset_1(C, A) => ~r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_subset_1)).
% 2.36/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.36/1.35  tff(f_74, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.36/1.35  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.36/1.35  tff(f_81, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.36/1.35  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.36/1.35  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.36/1.35  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.35  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.36/1.35  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.36/1.35  tff(c_125, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51), B_51) | k1_xboole_0=B_51 | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.35  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.35  tff(c_141, plain, (![B_52, A_53]: (~v1_xboole_0(B_52) | k1_xboole_0=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_125, c_2])).
% 2.36/1.35  tff(c_151, plain, (~v1_xboole_0('#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_40, c_141])).
% 2.36/1.35  tff(c_159, plain, (~v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_38, c_151])).
% 2.36/1.35  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.35  tff(c_68, plain, (![A_38, C_39, B_40]: (m1_subset_1(A_38, C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.36/1.35  tff(c_73, plain, (![A_38]: (m1_subset_1(A_38, k1_zfmisc_1('#skF_4')) | ~r2_hidden(A_38, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 2.36/1.35  tff(c_12, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.35  tff(c_52, plain, (![C_34, B_35, A_36]: (~v1_xboole_0(C_34) | ~m1_subset_1(B_35, k1_zfmisc_1(C_34)) | ~r2_hidden(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.36/1.35  tff(c_58, plain, (![A_8, A_36]: (~v1_xboole_0(A_8) | ~r2_hidden(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_52])).
% 2.36/1.35  tff(c_59, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_58])).
% 2.36/1.35  tff(c_36, plain, (k7_setfam_1('#skF_4', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.36/1.35  tff(c_97, plain, (![A_47, B_48]: (k7_setfam_1(A_47, k7_setfam_1(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.36/1.35  tff(c_102, plain, (k7_setfam_1('#skF_4', k7_setfam_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_40, c_97])).
% 2.36/1.35  tff(c_108, plain, (k7_setfam_1('#skF_4', k1_xboole_0)='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_102])).
% 2.36/1.35  tff(c_433, plain, (![A_91, D_92, B_93]: (r2_hidden(k3_subset_1(A_91, D_92), B_93) | ~r2_hidden(D_92, k7_setfam_1(A_91, B_93)) | ~m1_subset_1(D_92, k1_zfmisc_1(A_91)) | ~m1_subset_1(k7_setfam_1(A_91, B_93), k1_zfmisc_1(k1_zfmisc_1(A_91))) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.36/1.35  tff(c_439, plain, (![D_92]: (r2_hidden(k3_subset_1('#skF_4', D_92), k1_xboole_0) | ~r2_hidden(D_92, k7_setfam_1('#skF_4', k1_xboole_0)) | ~m1_subset_1(D_92, k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_4'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_108, c_433])).
% 2.36/1.35  tff(c_446, plain, (![D_92]: (r2_hidden(k3_subset_1('#skF_4', D_92), k1_xboole_0) | ~r2_hidden(D_92, '#skF_5') | ~m1_subset_1(D_92, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_40, c_108, c_439])).
% 2.36/1.35  tff(c_450, plain, (![D_94]: (~r2_hidden(D_94, '#skF_5') | ~m1_subset_1(D_94, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_59, c_446])).
% 2.36/1.35  tff(c_470, plain, (![A_95]: (~r2_hidden(A_95, '#skF_5'))), inference(resolution, [status(thm)], [c_73, c_450])).
% 2.36/1.35  tff(c_478, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_470])).
% 2.36/1.35  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_159, c_478])).
% 2.36/1.35  tff(c_486, plain, (![A_8]: (~v1_xboole_0(A_8))), inference(splitRight, [status(thm)], [c_58])).
% 2.36/1.35  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.35  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_486, c_6])).
% 2.36/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.36/1.35  
% 2.36/1.35  Inference rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Ref     : 0
% 2.36/1.35  #Sup     : 95
% 2.36/1.35  #Fact    : 0
% 2.36/1.35  #Define  : 0
% 2.36/1.35  #Split   : 6
% 2.36/1.35  #Chain   : 0
% 2.36/1.35  #Close   : 0
% 2.36/1.35  
% 2.36/1.35  Ordering : KBO
% 2.36/1.35  
% 2.36/1.35  Simplification rules
% 2.36/1.35  ----------------------
% 2.36/1.35  #Subsume      : 23
% 2.36/1.35  #Demod        : 37
% 2.36/1.35  #Tautology    : 21
% 2.36/1.35  #SimpNegUnit  : 12
% 2.36/1.35  #BackRed      : 2
% 2.36/1.35  
% 2.36/1.35  #Partial instantiations: 0
% 2.36/1.35  #Strategies tried      : 1
% 2.36/1.35  
% 2.36/1.35  Timing (in seconds)
% 2.36/1.35  ----------------------
% 2.36/1.35  Preprocessing        : 0.29
% 2.36/1.35  Parsing              : 0.15
% 2.36/1.35  CNF conversion       : 0.02
% 2.36/1.35  Main loop            : 0.27
% 2.36/1.35  Inferencing          : 0.09
% 2.36/1.35  Reduction            : 0.08
% 2.36/1.35  Demodulation         : 0.05
% 2.36/1.35  BG Simplification    : 0.02
% 2.36/1.35  Subsumption          : 0.07
% 2.36/1.35  Abstraction          : 0.01
% 2.36/1.35  MUC search           : 0.00
% 2.36/1.35  Cooper               : 0.00
% 2.36/1.35  Total                : 0.59
% 2.36/1.35  Index Insertion      : 0.00
% 2.36/1.35  Index Deletion       : 0.00
% 2.36/1.35  Index Matching       : 0.00
% 2.36/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
