%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:57 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   54 (  66 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 122 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_pre_topc(B,A)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B))))
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(c_59,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_1'(A_34,B_35),A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_68,plain,(
    ! [A_34] : r1_tarski(A_34,A_34) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | ~ m1_subset_1(A_28,k1_zfmisc_1(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_47,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_28,c_39])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51)
      | r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_6,c_71])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [A_61,B_62,B_63,B_64] :
      ( r2_hidden('#skF_1'(A_61,B_62),B_63)
      | ~ r1_tarski(B_64,B_63)
      | ~ r1_tarski(A_61,B_64)
      | r1_tarski(A_61,B_62) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_151,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_65,'#skF_6')
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_47,c_135])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_163,plain,(
    ! [A_65,B_66] :
      ( r1_tarski('#skF_1'(A_65,B_66),u1_struct_0('#skF_5'))
      | ~ r1_tarski(A_65,'#skF_6')
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_151,c_8])).

tff(c_32,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_30,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_164,plain,(
    ! [C_67,A_68,B_69] :
      ( m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(u1_struct_0(B_69)))
      | ~ m1_pre_topc(B_69,A_68)
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_247,plain,(
    ! [A_80,A_81,B_82] :
      ( m1_subset_1(A_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_pre_topc(B_82,A_81)
      | ~ l1_pre_topc(A_81)
      | ~ r1_tarski(A_80,u1_struct_0(B_82)) ) ),
    inference(resolution,[status(thm)],[c_22,c_164])).

tff(c_249,plain,(
    ! [A_80] :
      ( m1_subset_1(A_80,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ r1_tarski(A_80,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_30,c_247])).

tff(c_253,plain,(
    ! [A_83] :
      ( m1_subset_1(A_83,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski(A_83,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_249])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_261,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_84,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_253,c_20])).

tff(c_301,plain,(
    ! [A_87,B_88] :
      ( r1_tarski('#skF_1'(A_87,B_88),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_87,'#skF_6')
      | r1_tarski(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_163,c_261])).

tff(c_10,plain,(
    ! [C_10,A_6] :
      ( r2_hidden(C_10,k1_zfmisc_1(A_6))
      | ~ r1_tarski(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_53,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden('#skF_1'(A_32,B_33),B_33)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_32,A_6] :
      ( r1_tarski(A_32,k1_zfmisc_1(A_6))
      | ~ r1_tarski('#skF_1'(A_32,k1_zfmisc_1(A_6)),A_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_313,plain,(
    ! [A_89] :
      ( ~ r1_tarski(A_89,'#skF_6')
      | r1_tarski(A_89,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_301,c_58])).

tff(c_34,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ~ r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_34,c_26])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_313,c_38])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:56:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.71  
% 2.59/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.71  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > l1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 2.59/1.71  
% 2.59/1.71  %Foreground sorts:
% 2.59/1.71  
% 2.59/1.71  
% 2.59/1.71  %Background operators:
% 2.59/1.71  
% 2.59/1.71  
% 2.59/1.71  %Foreground operators:
% 2.59/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.59/1.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.59/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.71  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.71  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.71  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.59/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.59/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.59/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.59/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.71  
% 2.59/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.59/1.72  tff(f_64, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(B)))) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_tops_2)).
% 2.59/1.72  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.59/1.72  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.59/1.72  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.59/1.72  tff(c_59, plain, (![A_34, B_35]: (r2_hidden('#skF_1'(A_34, B_35), A_34) | r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.72  tff(c_68, plain, (![A_34]: (r1_tarski(A_34, A_34))), inference(resolution, [status(thm)], [c_59, c_4])).
% 2.59/1.72  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.72  tff(c_39, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | ~m1_subset_1(A_28, k1_zfmisc_1(B_29)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.72  tff(c_47, plain, (r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_28, c_39])).
% 2.59/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.72  tff(c_71, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.72  tff(c_100, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_1'(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51) | r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_6, c_71])).
% 2.59/1.72  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.72  tff(c_135, plain, (![A_61, B_62, B_63, B_64]: (r2_hidden('#skF_1'(A_61, B_62), B_63) | ~r1_tarski(B_64, B_63) | ~r1_tarski(A_61, B_64) | r1_tarski(A_61, B_62))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.59/1.72  tff(c_151, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski(A_65, '#skF_6') | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_47, c_135])).
% 2.59/1.72  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.72  tff(c_163, plain, (![A_65, B_66]: (r1_tarski('#skF_1'(A_65, B_66), u1_struct_0('#skF_5')) | ~r1_tarski(A_65, '#skF_6') | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_151, c_8])).
% 2.59/1.72  tff(c_32, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.72  tff(c_30, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.72  tff(c_22, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.72  tff(c_164, plain, (![C_67, A_68, B_69]: (m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(A_68))) | ~m1_subset_1(C_67, k1_zfmisc_1(u1_struct_0(B_69))) | ~m1_pre_topc(B_69, A_68) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.59/1.72  tff(c_247, plain, (![A_80, A_81, B_82]: (m1_subset_1(A_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_pre_topc(B_82, A_81) | ~l1_pre_topc(A_81) | ~r1_tarski(A_80, u1_struct_0(B_82)))), inference(resolution, [status(thm)], [c_22, c_164])).
% 2.59/1.72  tff(c_249, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~r1_tarski(A_80, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_30, c_247])).
% 2.59/1.72  tff(c_253, plain, (![A_83]: (m1_subset_1(A_83, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski(A_83, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_249])).
% 2.59/1.72  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.72  tff(c_261, plain, (![A_84]: (r1_tarski(A_84, u1_struct_0('#skF_4')) | ~r1_tarski(A_84, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_253, c_20])).
% 2.59/1.72  tff(c_301, plain, (![A_87, B_88]: (r1_tarski('#skF_1'(A_87, B_88), u1_struct_0('#skF_4')) | ~r1_tarski(A_87, '#skF_6') | r1_tarski(A_87, B_88))), inference(resolution, [status(thm)], [c_163, c_261])).
% 2.59/1.72  tff(c_10, plain, (![C_10, A_6]: (r2_hidden(C_10, k1_zfmisc_1(A_6)) | ~r1_tarski(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.59/1.72  tff(c_53, plain, (![A_32, B_33]: (~r2_hidden('#skF_1'(A_32, B_33), B_33) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.59/1.72  tff(c_58, plain, (![A_32, A_6]: (r1_tarski(A_32, k1_zfmisc_1(A_6)) | ~r1_tarski('#skF_1'(A_32, k1_zfmisc_1(A_6)), A_6))), inference(resolution, [status(thm)], [c_10, c_53])).
% 2.59/1.72  tff(c_313, plain, (![A_89]: (~r1_tarski(A_89, '#skF_6') | r1_tarski(A_89, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_301, c_58])).
% 2.59/1.72  tff(c_34, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.59/1.72  tff(c_26, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.59/1.72  tff(c_38, plain, (~r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_34, c_26])).
% 2.59/1.72  tff(c_334, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_313, c_38])).
% 2.59/1.72  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_334])).
% 2.59/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.72  
% 2.59/1.72  Inference rules
% 2.59/1.72  ----------------------
% 2.59/1.72  #Ref     : 0
% 2.59/1.72  #Sup     : 70
% 2.59/1.72  #Fact    : 0
% 2.59/1.72  #Define  : 0
% 2.59/1.72  #Split   : 2
% 2.59/1.72  #Chain   : 0
% 2.59/1.72  #Close   : 0
% 2.59/1.72  
% 2.59/1.72  Ordering : KBO
% 2.59/1.72  
% 2.59/1.72  Simplification rules
% 2.59/1.72  ----------------------
% 2.59/1.72  #Subsume      : 8
% 2.59/1.72  #Demod        : 3
% 2.59/1.72  #Tautology    : 5
% 2.59/1.72  #SimpNegUnit  : 0
% 2.59/1.72  #BackRed      : 0
% 2.59/1.72  
% 2.59/1.72  #Partial instantiations: 0
% 2.59/1.72  #Strategies tried      : 1
% 2.59/1.72  
% 2.59/1.72  Timing (in seconds)
% 2.59/1.72  ----------------------
% 2.59/1.72  Preprocessing        : 0.43
% 2.59/1.73  Parsing              : 0.23
% 2.59/1.73  CNF conversion       : 0.04
% 2.59/1.73  Main loop            : 0.39
% 2.59/1.73  Inferencing          : 0.15
% 2.59/1.73  Reduction            : 0.10
% 2.59/1.73  Demodulation         : 0.07
% 2.59/1.73  BG Simplification    : 0.02
% 2.59/1.73  Subsumption          : 0.09
% 2.59/1.73  Abstraction          : 0.02
% 2.59/1.73  MUC search           : 0.00
% 2.59/1.73  Cooper               : 0.00
% 2.59/1.73  Total                : 0.86
% 2.59/1.73  Index Insertion      : 0.00
% 2.59/1.73  Index Deletion       : 0.00
% 2.59/1.73  Index Matching       : 0.00
% 2.59/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
