%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:02 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 129 expanded)
%              Number of leaves         :   19 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 323 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( r2_hidden(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( v4_pre_topc(D,A)
                        & r1_tarski(B,D) )
                     => r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden('#skF_1'(A_35,B_36),B_36)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_31,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_26])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,(
    ! [C_41,A_42,B_43] :
      ( r2_hidden(C_41,A_42)
      | ~ r2_hidden(C_41,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [A_50,B_51,A_52] :
      ( r2_hidden('#skF_1'(A_50,B_51),A_52)
      | ~ m1_subset_1(A_50,k1_zfmisc_1(A_52))
      | r1_tarski(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_53,A_54] :
      ( ~ m1_subset_1(A_53,k1_zfmisc_1(A_54))
      | r1_tarski(A_53,A_54) ) ),
    inference(resolution,[status(thm)],[c_59,c_4])).

tff(c_75,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_71])).

tff(c_32,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(C_37,B_38)
      | ~ r2_hidden(C_37,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_44,B_45,B_46] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_46)
      | ~ r1_tarski(A_44,B_46)
      | r1_tarski(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_76,plain,(
    ! [A_55,B_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski(A_55,B_58)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_83,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_59,'#skF_4')
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_75,c_76])).

tff(c_93,plain,(
    ! [A_59,B_60,B_2] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_2)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_2)
      | ~ r1_tarski(A_59,'#skF_4')
      | r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_83,c_2])).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_40,plain,(
    ! [A_1,B_2,A_42] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_42)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(A_42))
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_37])).

tff(c_184,plain,(
    ! [B_85,A_86,C_87] :
      ( r1_tarski(B_85,'#skF_2'(A_86,B_85,C_87))
      | r2_hidden(C_87,k2_pre_topc(A_86,B_85))
      | ~ r2_hidden(C_87,u1_struct_0(A_86))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_86)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_186,plain,(
    ! [C_87] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4',C_87))
      | r2_hidden(C_87,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden(C_87,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_22,c_184])).

tff(c_191,plain,(
    ! [C_88] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4',C_88))
      | r2_hidden(C_88,k2_pre_topc('#skF_3','#skF_4'))
      | ~ r2_hidden(C_88,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_186])).

tff(c_378,plain,(
    ! [A_145] :
      ( r1_tarski(A_145,k2_pre_topc('#skF_3','#skF_4'))
      | r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_1'(A_145,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ r2_hidden('#skF_1'(A_145,k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_191,c_4])).

tff(c_415,plain,(
    ! [A_1] :
      ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4','#skF_1'(A_1,k2_pre_topc('#skF_3','#skF_4'))))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | r1_tarski(A_1,k2_pre_topc('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_40,c_378])).

tff(c_35,plain,(
    ! [A_1,B_2,B_38] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_38)
      | ~ r1_tarski(A_1,B_38)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_95,plain,(
    ! [C_61,A_62,B_63] :
      ( ~ r2_hidden(C_61,'#skF_2'(A_62,B_63,C_61))
      | r2_hidden(C_61,k2_pre_topc(A_62,B_63))
      | ~ r2_hidden(C_61,u1_struct_0(A_62))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_734,plain,(
    ! [A_165,B_166,A_167,B_168] :
      ( r2_hidden('#skF_1'(A_165,B_166),k2_pre_topc(A_167,B_168))
      | ~ r2_hidden('#skF_1'(A_165,B_166),u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167)
      | ~ r1_tarski(A_165,'#skF_2'(A_167,B_168,'#skF_1'(A_165,B_166)))
      | r1_tarski(A_165,B_166) ) ),
    inference(resolution,[status(thm)],[c_35,c_95])).

tff(c_740,plain,
    ( r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | ~ l1_pre_topc('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_415,c_734])).

tff(c_762,plain,
    ( r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3'))
    | r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_740])).

tff(c_763,plain,
    ( r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4'))
    | ~ r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_762])).

tff(c_781,plain,(
    ~ r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_763])).

tff(c_787,plain,
    ( ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_93,c_781])).

tff(c_806,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_31,c_787])).

tff(c_808,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_806])).

tff(c_809,plain,(
    r2_hidden('#skF_1'('#skF_4',k2_pre_topc('#skF_3','#skF_4')),k2_pre_topc('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_763])).

tff(c_858,plain,(
    r1_tarski('#skF_4',k2_pre_topc('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_809,c_4])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_858])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.63/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.58  
% 3.63/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.59  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.63/1.59  
% 3.63/1.59  %Foreground sorts:
% 3.63/1.59  
% 3.63/1.59  
% 3.63/1.59  %Background operators:
% 3.63/1.59  
% 3.63/1.59  
% 3.63/1.59  %Foreground operators:
% 3.63/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.63/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.63/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.63/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.63/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.63/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.63/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.63/1.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.63/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.63/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.63/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.63/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.63/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.63/1.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.63/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.63/1.59  
% 3.63/1.60  tff(f_66, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_pre_topc)).
% 3.63/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.63/1.60  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.63/1.60  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_pre_topc)).
% 3.63/1.60  tff(c_20, plain, (~r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.63/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.60  tff(c_26, plain, (![A_35, B_36]: (~r2_hidden('#skF_1'(A_35, B_36), B_36) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.60  tff(c_31, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_26])).
% 3.63/1.60  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.63/1.60  tff(c_37, plain, (![C_41, A_42, B_43]: (r2_hidden(C_41, A_42) | ~r2_hidden(C_41, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.63/1.60  tff(c_59, plain, (![A_50, B_51, A_52]: (r2_hidden('#skF_1'(A_50, B_51), A_52) | ~m1_subset_1(A_50, k1_zfmisc_1(A_52)) | r1_tarski(A_50, B_51))), inference(resolution, [status(thm)], [c_6, c_37])).
% 3.63/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.60  tff(c_71, plain, (![A_53, A_54]: (~m1_subset_1(A_53, k1_zfmisc_1(A_54)) | r1_tarski(A_53, A_54))), inference(resolution, [status(thm)], [c_59, c_4])).
% 3.63/1.60  tff(c_75, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_71])).
% 3.63/1.60  tff(c_32, plain, (![C_37, B_38, A_39]: (r2_hidden(C_37, B_38) | ~r2_hidden(C_37, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.60  tff(c_41, plain, (![A_44, B_45, B_46]: (r2_hidden('#skF_1'(A_44, B_45), B_46) | ~r1_tarski(A_44, B_46) | r1_tarski(A_44, B_45))), inference(resolution, [status(thm)], [c_6, c_32])).
% 3.63/1.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.63/1.60  tff(c_76, plain, (![A_55, B_56, B_57, B_58]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski(A_55, B_58) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_41, c_2])).
% 3.63/1.60  tff(c_83, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), u1_struct_0('#skF_3')) | ~r1_tarski(A_59, '#skF_4') | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_75, c_76])).
% 3.63/1.60  tff(c_93, plain, (![A_59, B_60, B_2]: (r2_hidden('#skF_1'(A_59, B_60), B_2) | ~r1_tarski(u1_struct_0('#skF_3'), B_2) | ~r1_tarski(A_59, '#skF_4') | r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_83, c_2])).
% 3.63/1.60  tff(c_24, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.63/1.60  tff(c_40, plain, (![A_1, B_2, A_42]: (r2_hidden('#skF_1'(A_1, B_2), A_42) | ~m1_subset_1(A_1, k1_zfmisc_1(A_42)) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_37])).
% 3.63/1.60  tff(c_184, plain, (![B_85, A_86, C_87]: (r1_tarski(B_85, '#skF_2'(A_86, B_85, C_87)) | r2_hidden(C_87, k2_pre_topc(A_86, B_85)) | ~r2_hidden(C_87, u1_struct_0(A_86)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_86))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.60  tff(c_186, plain, (![C_87]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', C_87)) | r2_hidden(C_87, k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden(C_87, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_184])).
% 3.63/1.60  tff(c_191, plain, (![C_88]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', C_88)) | r2_hidden(C_88, k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden(C_88, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_186])).
% 3.63/1.60  tff(c_378, plain, (![A_145]: (r1_tarski(A_145, k2_pre_topc('#skF_3', '#skF_4')) | r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_145, k2_pre_topc('#skF_3', '#skF_4')))) | ~r2_hidden('#skF_1'(A_145, k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_191, c_4])).
% 3.63/1.60  tff(c_415, plain, (![A_1]: (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4', '#skF_1'(A_1, k2_pre_topc('#skF_3', '#skF_4')))) | ~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(A_1, k2_pre_topc('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_40, c_378])).
% 3.63/1.60  tff(c_35, plain, (![A_1, B_2, B_38]: (r2_hidden('#skF_1'(A_1, B_2), B_38) | ~r1_tarski(A_1, B_38) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_32])).
% 3.63/1.60  tff(c_95, plain, (![C_61, A_62, B_63]: (~r2_hidden(C_61, '#skF_2'(A_62, B_63, C_61)) | r2_hidden(C_61, k2_pre_topc(A_62, B_63)) | ~r2_hidden(C_61, u1_struct_0(A_62)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.63/1.60  tff(c_734, plain, (![A_165, B_166, A_167, B_168]: (r2_hidden('#skF_1'(A_165, B_166), k2_pre_topc(A_167, B_168)) | ~r2_hidden('#skF_1'(A_165, B_166), u1_struct_0(A_167)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167) | ~r1_tarski(A_165, '#skF_2'(A_167, B_168, '#skF_1'(A_165, B_166))) | r1_tarski(A_165, B_166))), inference(resolution, [status(thm)], [c_35, c_95])).
% 3.63/1.60  tff(c_740, plain, (r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_415, c_734])).
% 3.63/1.60  tff(c_762, plain, (r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3')) | r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_740])).
% 3.63/1.60  tff(c_763, plain, (r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4')) | ~r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_20, c_762])).
% 3.63/1.60  tff(c_781, plain, (~r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_763])).
% 3.63/1.60  tff(c_787, plain, (~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_93, c_781])).
% 3.63/1.60  tff(c_806, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_31, c_787])).
% 3.63/1.60  tff(c_808, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_806])).
% 3.63/1.60  tff(c_809, plain, (r2_hidden('#skF_1'('#skF_4', k2_pre_topc('#skF_3', '#skF_4')), k2_pre_topc('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_763])).
% 3.63/1.60  tff(c_858, plain, (r1_tarski('#skF_4', k2_pre_topc('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_809, c_4])).
% 3.63/1.60  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_858])).
% 3.63/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/1.60  
% 3.63/1.60  Inference rules
% 3.63/1.60  ----------------------
% 3.63/1.60  #Ref     : 0
% 3.63/1.60  #Sup     : 214
% 3.63/1.60  #Fact    : 0
% 3.63/1.60  #Define  : 0
% 3.63/1.60  #Split   : 8
% 3.63/1.60  #Chain   : 0
% 3.63/1.60  #Close   : 0
% 3.63/1.60  
% 3.63/1.60  Ordering : KBO
% 3.63/1.60  
% 3.63/1.60  Simplification rules
% 3.63/1.60  ----------------------
% 3.63/1.60  #Subsume      : 66
% 3.63/1.60  #Demod        : 36
% 3.63/1.60  #Tautology    : 3
% 3.63/1.60  #SimpNegUnit  : 13
% 3.63/1.60  #BackRed      : 0
% 3.63/1.60  
% 3.63/1.60  #Partial instantiations: 0
% 3.63/1.60  #Strategies tried      : 1
% 3.63/1.60  
% 3.63/1.60  Timing (in seconds)
% 3.63/1.60  ----------------------
% 3.63/1.60  Preprocessing        : 0.27
% 3.63/1.60  Parsing              : 0.15
% 3.63/1.60  CNF conversion       : 0.02
% 3.63/1.60  Main loop            : 0.53
% 3.63/1.60  Inferencing          : 0.17
% 3.63/1.60  Reduction            : 0.13
% 3.63/1.60  Demodulation         : 0.08
% 3.63/1.60  BG Simplification    : 0.02
% 3.63/1.60  Subsumption          : 0.18
% 3.63/1.60  Abstraction          : 0.02
% 3.63/1.60  MUC search           : 0.00
% 3.63/1.60  Cooper               : 0.00
% 3.63/1.60  Total                : 0.83
% 3.63/1.60  Index Insertion      : 0.00
% 3.63/1.60  Index Deletion       : 0.00
% 3.63/1.60  Index Matching       : 0.00
% 3.63/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
