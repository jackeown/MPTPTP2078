%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:52 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 133 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 322 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_33,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_34,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_32])).

tff(c_159,plain,(
    ! [A_60,B_61] :
      ( r2_hidden('#skF_2'(A_60,B_61),B_61)
      | v1_tops_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_161,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_159])).

tff(c_164,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_161])).

tff(c_165,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_164])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_175,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_2'('#skF_3','#skF_4'),B_62)
      | ~ r1_tarski('#skF_4',B_62) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_47,plain,(
    ! [A_31,C_32,B_33] :
      ( m1_subset_1(A_31,C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_31,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [A_31] :
      ( m1_subset_1(A_31,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_47])).

tff(c_72,plain,(
    ! [B_42,A_43] :
      ( v3_pre_topc(B_42,A_43)
      | ~ r2_hidden(B_42,u1_pre_topc(A_43))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_75,plain,(
    ! [A_31] :
      ( v3_pre_topc(A_31,'#skF_3')
      | ~ r2_hidden(A_31,u1_pre_topc('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_72])).

tff(c_78,plain,(
    ! [A_31] :
      ( v3_pre_topc(A_31,'#skF_3')
      | ~ r2_hidden(A_31,u1_pre_topc('#skF_3'))
      | ~ r2_hidden(A_31,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_75])).

tff(c_182,plain,
    ( v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_175,c_78])).

tff(c_192,plain,(
    v3_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_165,c_182])).

tff(c_239,plain,(
    ! [A_66,B_67] :
      ( ~ v3_pre_topc('#skF_2'(A_66,B_67),A_66)
      | v1_tops_2(B_67,A_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66))))
      | ~ l1_pre_topc(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_241,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_192,c_239])).

tff(c_244,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_244])).

tff(c_247,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_252,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_1'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_257,plain,(
    ! [A_70] : r1_tarski(A_70,A_70) ),
    inference(resolution,[status(thm)],[c_252,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_259,plain,(
    ! [C_73,B_74,A_75] :
      ( r2_hidden(C_73,B_74)
      | ~ r2_hidden(C_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_262,plain,(
    ! [A_1,B_2,B_74] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_74)
      | ~ r1_tarski(A_1,B_74)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_248,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_263,plain,(
    ! [A_76,C_77,B_78] :
      ( m1_subset_1(A_76,C_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(C_77))
      | ~ r2_hidden(A_76,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_266,plain,(
    ! [A_76] :
      ( m1_subset_1(A_76,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_263])).

tff(c_387,plain,(
    ! [C_117,A_118,B_119] :
      ( v3_pre_topc(C_117,A_118)
      | ~ r2_hidden(C_117,B_119)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(u1_struct_0(A_118)))
      | ~ v1_tops_2(B_119,A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_118))))
      | ~ l1_pre_topc(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_435,plain,(
    ! [A_141,B_142,A_143] :
      ( v3_pre_topc('#skF_1'(A_141,B_142),A_143)
      | ~ m1_subset_1('#skF_1'(A_141,B_142),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ v1_tops_2(A_141,A_143)
      | ~ m1_subset_1(A_141,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143))))
      | ~ l1_pre_topc(A_143)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_387])).

tff(c_439,plain,(
    ! [A_141,B_142] :
      ( v3_pre_topc('#skF_1'(A_141,B_142),'#skF_3')
      | ~ v1_tops_2(A_141,'#skF_3')
      | ~ m1_subset_1(A_141,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | ~ l1_pre_topc('#skF_3')
      | r1_tarski(A_141,B_142)
      | ~ r2_hidden('#skF_1'(A_141,B_142),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_266,c_435])).

tff(c_443,plain,(
    ! [A_144,B_145] :
      ( v3_pre_topc('#skF_1'(A_144,B_145),'#skF_3')
      | ~ v1_tops_2(A_144,'#skF_3')
      | ~ m1_subset_1(A_144,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
      | r1_tarski(A_144,B_145)
      | ~ r2_hidden('#skF_1'(A_144,B_145),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_439])).

tff(c_445,plain,(
    ! [B_145] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_145),'#skF_3')
      | ~ v1_tops_2('#skF_4','#skF_3')
      | r1_tarski('#skF_4',B_145)
      | ~ r2_hidden('#skF_1'('#skF_4',B_145),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_443])).

tff(c_456,plain,(
    ! [B_150] :
      ( v3_pre_topc('#skF_1'('#skF_4',B_150),'#skF_3')
      | r1_tarski('#skF_4',B_150)
      | ~ r2_hidden('#skF_1'('#skF_4',B_150),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_445])).

tff(c_271,plain,(
    ! [B_80,A_81] :
      ( r2_hidden(B_80,u1_pre_topc(A_81))
      | ~ v3_pre_topc(B_80,A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_274,plain,(
    ! [A_76] :
      ( r2_hidden(A_76,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_76,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ r2_hidden(A_76,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_266,c_271])).

tff(c_282,plain,(
    ! [A_84] :
      ( r2_hidden(A_84,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc(A_84,'#skF_3')
      | ~ r2_hidden(A_84,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_274])).

tff(c_293,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_pre_topc('#skF_3'))
      | ~ v3_pre_topc('#skF_1'(A_1,u1_pre_topc('#skF_3')),'#skF_3')
      | ~ r2_hidden('#skF_1'(A_1,u1_pre_topc('#skF_3')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_282,c_4])).

tff(c_460,plain,
    ( r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ r2_hidden('#skF_1'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_456,c_293])).

tff(c_463,plain,(
    ~ r2_hidden('#skF_1'('#skF_4',u1_pre_topc('#skF_3')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_247,c_460])).

tff(c_466,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(resolution,[status(thm)],[c_262,c_463])).

tff(c_472,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_466])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_247,c_472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.74/1.40  
% 2.74/1.40  %Foreground sorts:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Background operators:
% 2.74/1.40  
% 2.74/1.40  
% 2.74/1.40  %Foreground operators:
% 2.74/1.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.74/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.40  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.74/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.74/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.74/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.40  
% 2.74/1.42  tff(f_71, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 2.74/1.42  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 2.74/1.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.74/1.42  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.74/1.42  tff(f_47, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.74/1.42  tff(c_26, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_3')) | ~v1_tops_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.42  tff(c_33, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 2.74/1.42  tff(c_24, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.42  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.42  tff(c_32, plain, (v1_tops_2('#skF_4', '#skF_3') | r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.74/1.42  tff(c_34, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_33, c_32])).
% 2.74/1.42  tff(c_159, plain, (![A_60, B_61]: (r2_hidden('#skF_2'(A_60, B_61), B_61) | v1_tops_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.42  tff(c_161, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_22, c_159])).
% 2.74/1.42  tff(c_164, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_161])).
% 2.74/1.42  tff(c_165, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_33, c_164])).
% 2.74/1.42  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.42  tff(c_175, plain, (![B_62]: (r2_hidden('#skF_2'('#skF_3', '#skF_4'), B_62) | ~r1_tarski('#skF_4', B_62))), inference(resolution, [status(thm)], [c_165, c_2])).
% 2.74/1.42  tff(c_47, plain, (![A_31, C_32, B_33]: (m1_subset_1(A_31, C_32) | ~m1_subset_1(B_33, k1_zfmisc_1(C_32)) | ~r2_hidden(A_31, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.42  tff(c_50, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_47])).
% 2.74/1.42  tff(c_72, plain, (![B_42, A_43]: (v3_pre_topc(B_42, A_43) | ~r2_hidden(B_42, u1_pre_topc(A_43)) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_43))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.42  tff(c_75, plain, (![A_31]: (v3_pre_topc(A_31, '#skF_3') | ~r2_hidden(A_31, u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_31, '#skF_4'))), inference(resolution, [status(thm)], [c_50, c_72])).
% 2.74/1.42  tff(c_78, plain, (![A_31]: (v3_pre_topc(A_31, '#skF_3') | ~r2_hidden(A_31, u1_pre_topc('#skF_3')) | ~r2_hidden(A_31, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_75])).
% 2.74/1.42  tff(c_182, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_175, c_78])).
% 2.74/1.42  tff(c_192, plain, (v3_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_165, c_182])).
% 2.74/1.42  tff(c_239, plain, (![A_66, B_67]: (~v3_pre_topc('#skF_2'(A_66, B_67), A_66) | v1_tops_2(B_67, A_66) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_66)))) | ~l1_pre_topc(A_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.42  tff(c_241, plain, (v1_tops_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_192, c_239])).
% 2.74/1.42  tff(c_244, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_241])).
% 2.74/1.42  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_244])).
% 2.74/1.42  tff(c_247, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.74/1.42  tff(c_252, plain, (![A_70, B_71]: (r2_hidden('#skF_1'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.42  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.42  tff(c_257, plain, (![A_70]: (r1_tarski(A_70, A_70))), inference(resolution, [status(thm)], [c_252, c_4])).
% 2.74/1.42  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.42  tff(c_259, plain, (![C_73, B_74, A_75]: (r2_hidden(C_73, B_74) | ~r2_hidden(C_73, A_75) | ~r1_tarski(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.74/1.42  tff(c_262, plain, (![A_1, B_2, B_74]: (r2_hidden('#skF_1'(A_1, B_2), B_74) | ~r1_tarski(A_1, B_74) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_259])).
% 2.74/1.42  tff(c_248, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.74/1.42  tff(c_263, plain, (![A_76, C_77, B_78]: (m1_subset_1(A_76, C_77) | ~m1_subset_1(B_78, k1_zfmisc_1(C_77)) | ~r2_hidden(A_76, B_78))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.42  tff(c_266, plain, (![A_76]: (m1_subset_1(A_76, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_263])).
% 2.74/1.42  tff(c_387, plain, (![C_117, A_118, B_119]: (v3_pre_topc(C_117, A_118) | ~r2_hidden(C_117, B_119) | ~m1_subset_1(C_117, k1_zfmisc_1(u1_struct_0(A_118))) | ~v1_tops_2(B_119, A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_118)))) | ~l1_pre_topc(A_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.74/1.42  tff(c_435, plain, (![A_141, B_142, A_143]: (v3_pre_topc('#skF_1'(A_141, B_142), A_143) | ~m1_subset_1('#skF_1'(A_141, B_142), k1_zfmisc_1(u1_struct_0(A_143))) | ~v1_tops_2(A_141, A_143) | ~m1_subset_1(A_141, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))) | ~l1_pre_topc(A_143) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_6, c_387])).
% 2.74/1.42  tff(c_439, plain, (![A_141, B_142]: (v3_pre_topc('#skF_1'(A_141, B_142), '#skF_3') | ~v1_tops_2(A_141, '#skF_3') | ~m1_subset_1(A_141, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3') | r1_tarski(A_141, B_142) | ~r2_hidden('#skF_1'(A_141, B_142), '#skF_4'))), inference(resolution, [status(thm)], [c_266, c_435])).
% 2.74/1.42  tff(c_443, plain, (![A_144, B_145]: (v3_pre_topc('#skF_1'(A_144, B_145), '#skF_3') | ~v1_tops_2(A_144, '#skF_3') | ~m1_subset_1(A_144, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | r1_tarski(A_144, B_145) | ~r2_hidden('#skF_1'(A_144, B_145), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_439])).
% 2.74/1.42  tff(c_445, plain, (![B_145]: (v3_pre_topc('#skF_1'('#skF_4', B_145), '#skF_3') | ~v1_tops_2('#skF_4', '#skF_3') | r1_tarski('#skF_4', B_145) | ~r2_hidden('#skF_1'('#skF_4', B_145), '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_443])).
% 2.74/1.42  tff(c_456, plain, (![B_150]: (v3_pre_topc('#skF_1'('#skF_4', B_150), '#skF_3') | r1_tarski('#skF_4', B_150) | ~r2_hidden('#skF_1'('#skF_4', B_150), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_248, c_445])).
% 2.74/1.42  tff(c_271, plain, (![B_80, A_81]: (r2_hidden(B_80, u1_pre_topc(A_81)) | ~v3_pre_topc(B_80, A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.74/1.42  tff(c_274, plain, (![A_76]: (r2_hidden(A_76, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_76, '#skF_3') | ~l1_pre_topc('#skF_3') | ~r2_hidden(A_76, '#skF_4'))), inference(resolution, [status(thm)], [c_266, c_271])).
% 2.74/1.42  tff(c_282, plain, (![A_84]: (r2_hidden(A_84, u1_pre_topc('#skF_3')) | ~v3_pre_topc(A_84, '#skF_3') | ~r2_hidden(A_84, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_274])).
% 2.74/1.42  tff(c_293, plain, (![A_1]: (r1_tarski(A_1, u1_pre_topc('#skF_3')) | ~v3_pre_topc('#skF_1'(A_1, u1_pre_topc('#skF_3')), '#skF_3') | ~r2_hidden('#skF_1'(A_1, u1_pre_topc('#skF_3')), '#skF_4'))), inference(resolution, [status(thm)], [c_282, c_4])).
% 2.74/1.42  tff(c_460, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3')) | ~r2_hidden('#skF_1'('#skF_4', u1_pre_topc('#skF_3')), '#skF_4')), inference(resolution, [status(thm)], [c_456, c_293])).
% 2.74/1.42  tff(c_463, plain, (~r2_hidden('#skF_1'('#skF_4', u1_pre_topc('#skF_3')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_247, c_247, c_460])).
% 2.74/1.42  tff(c_466, plain, (~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_262, c_463])).
% 2.74/1.42  tff(c_472, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_466])).
% 2.74/1.42  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_247, c_472])).
% 2.74/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  Inference rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Ref     : 0
% 2.74/1.42  #Sup     : 89
% 2.74/1.42  #Fact    : 0
% 2.74/1.42  #Define  : 0
% 2.74/1.42  #Split   : 5
% 2.74/1.42  #Chain   : 0
% 2.74/1.42  #Close   : 0
% 2.74/1.42  
% 2.74/1.42  Ordering : KBO
% 2.74/1.42  
% 2.74/1.42  Simplification rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Subsume      : 9
% 2.74/1.42  #Demod        : 28
% 2.74/1.42  #Tautology    : 15
% 2.74/1.42  #SimpNegUnit  : 6
% 2.74/1.42  #BackRed      : 0
% 2.74/1.42  
% 2.74/1.42  #Partial instantiations: 0
% 2.74/1.42  #Strategies tried      : 1
% 2.74/1.42  
% 2.74/1.42  Timing (in seconds)
% 2.74/1.42  ----------------------
% 2.74/1.42  Preprocessing        : 0.29
% 2.74/1.42  Parsing              : 0.16
% 2.74/1.42  CNF conversion       : 0.02
% 2.74/1.42  Main loop            : 0.35
% 2.74/1.42  Inferencing          : 0.14
% 2.74/1.42  Reduction            : 0.09
% 2.74/1.42  Demodulation         : 0.05
% 2.74/1.42  BG Simplification    : 0.02
% 2.74/1.42  Subsumption          : 0.08
% 2.74/1.42  Abstraction          : 0.01
% 2.74/1.42  MUC search           : 0.00
% 2.74/1.42  Cooper               : 0.00
% 2.74/1.42  Total                : 0.68
% 2.74/1.42  Index Insertion      : 0.00
% 2.74/1.42  Index Deletion       : 0.00
% 2.74/1.42  Index Matching       : 0.00
% 2.74/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
