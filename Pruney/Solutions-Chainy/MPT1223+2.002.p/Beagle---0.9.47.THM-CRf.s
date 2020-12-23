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
% DateTime   : Thu Dec  3 10:20:26 EST 2020

% Result     : Theorem 9.27s
% Output     : CNFRefutation 9.27s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  104 ( 156 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v4_pre_topc(B,A)
                    & r1_tarski(C,B) )
                 => r1_tarski(k2_pre_topc(A,C),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
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

tff(c_24,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_42,B_43] :
      ( ~ r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_55,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_70,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k2_pre_topc(A_51,B_52),k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_74,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k2_pre_topc(A_51,B_52),u1_struct_0(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_70,c_8])).

tff(c_57,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_61,plain,(
    ! [A_48,B_49,B_50] :
      ( r2_hidden('#skF_1'(A_48,B_49),B_50)
      | ~ r1_tarski(A_48,B_50)
      | r1_tarski(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

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
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_560,plain,(
    ! [A_134,B_135,A_136,B_137] :
      ( r2_hidden('#skF_1'(A_134,B_135),u1_struct_0(A_136))
      | ~ r1_tarski(A_134,k2_pre_topc(A_136,B_137))
      | r1_tarski(A_134,B_135)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_74,c_76])).

tff(c_564,plain,(
    ! [A_136,B_137,B_135] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_136,B_137),B_135),u1_struct_0(A_136))
      | r1_tarski(k2_pre_topc(A_136,B_137),B_135)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_55,c_560])).

tff(c_26,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_732,plain,(
    ! [C_148,D_149,B_150,A_151] :
      ( r2_hidden(C_148,D_149)
      | ~ r1_tarski(B_150,D_149)
      | ~ v4_pre_topc(D_149,A_151)
      | ~ m1_subset_1(D_149,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ r2_hidden(C_148,k2_pre_topc(A_151,B_150))
      | ~ r2_hidden(C_148,u1_struct_0(A_151))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_808,plain,(
    ! [C_157,A_158] :
      ( r2_hidden(C_157,'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_158)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ r2_hidden(C_157,k2_pre_topc(A_158,'#skF_5'))
      | ~ r2_hidden(C_157,u1_struct_0(A_158))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(resolution,[status(thm)],[c_26,c_732])).

tff(c_5568,plain,(
    ! [A_367,B_368] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_367,'#skF_5'),B_368),'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_367)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ r2_hidden('#skF_1'(k2_pre_topc(A_367,'#skF_5'),B_368),u1_struct_0(A_367))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_367)))
      | ~ l1_pre_topc(A_367)
      | r1_tarski(k2_pre_topc(A_367,'#skF_5'),B_368) ) ),
    inference(resolution,[status(thm)],[c_6,c_808])).

tff(c_10114,plain,(
    ! [A_537,B_538] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_537,'#skF_5'),B_538),'#skF_4')
      | ~ v4_pre_topc('#skF_4',A_537)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_537)))
      | r1_tarski(k2_pre_topc(A_537,'#skF_5'),B_538)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_537)))
      | ~ l1_pre_topc(A_537) ) ),
    inference(resolution,[status(thm)],[c_564,c_5568])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10447,plain,(
    ! [A_557] :
      ( ~ v4_pre_topc('#skF_4',A_557)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_557)))
      | r1_tarski(k2_pre_topc(A_557,'#skF_5'),'#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_557)))
      | ~ l1_pre_topc(A_557) ) ),
    inference(resolution,[status(thm)],[c_10114,c_4])).

tff(c_10453,plain,
    ( ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_10447])).

tff(c_10457,plain,(
    r1_tarski(k2_pre_topc('#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_28,c_10453])).

tff(c_10459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_10457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.27/3.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.25  
% 9.27/3.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.26  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 9.27/3.26  
% 9.27/3.26  %Foreground sorts:
% 9.27/3.26  
% 9.27/3.26  
% 9.27/3.26  %Background operators:
% 9.27/3.26  
% 9.27/3.26  
% 9.27/3.26  %Foreground operators:
% 9.27/3.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.27/3.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.27/3.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.27/3.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.27/3.26  tff('#skF_5', type, '#skF_5': $i).
% 9.27/3.26  tff('#skF_3', type, '#skF_3': $i).
% 9.27/3.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.27/3.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.27/3.26  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 9.27/3.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.27/3.26  tff('#skF_4', type, '#skF_4': $i).
% 9.27/3.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.27/3.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.27/3.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.27/3.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 9.27/3.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.27/3.26  
% 9.27/3.27  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & r1_tarski(C, B)) => r1_tarski(k2_pre_topc(A, C), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_tops_1)).
% 9.27/3.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 9.27/3.27  tff(f_42, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 9.27/3.27  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.27/3.27  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_pre_topc)).
% 9.27/3.27  tff(c_24, plain, (~r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.27/3.27  tff(c_34, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.27/3.27  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.27/3.27  tff(c_28, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.27/3.27  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.27/3.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.27  tff(c_50, plain, (![A_42, B_43]: (~r2_hidden('#skF_1'(A_42, B_43), B_43) | r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.27  tff(c_55, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_50])).
% 9.27/3.27  tff(c_70, plain, (![A_51, B_52]: (m1_subset_1(k2_pre_topc(A_51, B_52), k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.27/3.27  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 9.27/3.27  tff(c_74, plain, (![A_51, B_52]: (r1_tarski(k2_pre_topc(A_51, B_52), u1_struct_0(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(resolution, [status(thm)], [c_70, c_8])).
% 9.27/3.27  tff(c_57, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.27  tff(c_61, plain, (![A_48, B_49, B_50]: (r2_hidden('#skF_1'(A_48, B_49), B_50) | ~r1_tarski(A_48, B_50) | r1_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_6, c_57])).
% 9.27/3.27  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.27  tff(c_76, plain, (![A_55, B_56, B_57, B_58]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski(A_55, B_58) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_61, c_2])).
% 9.27/3.27  tff(c_560, plain, (![A_134, B_135, A_136, B_137]: (r2_hidden('#skF_1'(A_134, B_135), u1_struct_0(A_136)) | ~r1_tarski(A_134, k2_pre_topc(A_136, B_137)) | r1_tarski(A_134, B_135) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_74, c_76])).
% 9.27/3.27  tff(c_564, plain, (![A_136, B_137, B_135]: (r2_hidden('#skF_1'(k2_pre_topc(A_136, B_137), B_135), u1_struct_0(A_136)) | r1_tarski(k2_pre_topc(A_136, B_137), B_135) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_55, c_560])).
% 9.27/3.27  tff(c_26, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.27/3.27  tff(c_732, plain, (![C_148, D_149, B_150, A_151]: (r2_hidden(C_148, D_149) | ~r1_tarski(B_150, D_149) | ~v4_pre_topc(D_149, A_151) | ~m1_subset_1(D_149, k1_zfmisc_1(u1_struct_0(A_151))) | ~r2_hidden(C_148, k2_pre_topc(A_151, B_150)) | ~r2_hidden(C_148, u1_struct_0(A_151)) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.27/3.27  tff(c_808, plain, (![C_157, A_158]: (r2_hidden(C_157, '#skF_4') | ~v4_pre_topc('#skF_4', A_158) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_158))) | ~r2_hidden(C_157, k2_pre_topc(A_158, '#skF_5')) | ~r2_hidden(C_157, u1_struct_0(A_158)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(resolution, [status(thm)], [c_26, c_732])).
% 9.27/3.27  tff(c_5568, plain, (![A_367, B_368]: (r2_hidden('#skF_1'(k2_pre_topc(A_367, '#skF_5'), B_368), '#skF_4') | ~v4_pre_topc('#skF_4', A_367) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_367))) | ~r2_hidden('#skF_1'(k2_pre_topc(A_367, '#skF_5'), B_368), u1_struct_0(A_367)) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_367))) | ~l1_pre_topc(A_367) | r1_tarski(k2_pre_topc(A_367, '#skF_5'), B_368))), inference(resolution, [status(thm)], [c_6, c_808])).
% 9.27/3.27  tff(c_10114, plain, (![A_537, B_538]: (r2_hidden('#skF_1'(k2_pre_topc(A_537, '#skF_5'), B_538), '#skF_4') | ~v4_pre_topc('#skF_4', A_537) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_537))) | r1_tarski(k2_pre_topc(A_537, '#skF_5'), B_538) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_537))) | ~l1_pre_topc(A_537))), inference(resolution, [status(thm)], [c_564, c_5568])).
% 9.27/3.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.27/3.27  tff(c_10447, plain, (![A_557]: (~v4_pre_topc('#skF_4', A_557) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_557))) | r1_tarski(k2_pre_topc(A_557, '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_557))) | ~l1_pre_topc(A_557))), inference(resolution, [status(thm)], [c_10114, c_4])).
% 9.27/3.27  tff(c_10453, plain, (~v4_pre_topc('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_10447])).
% 9.27/3.27  tff(c_10457, plain, (r1_tarski(k2_pre_topc('#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_28, c_10453])).
% 9.27/3.27  tff(c_10459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_10457])).
% 9.27/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.27/3.27  
% 9.27/3.27  Inference rules
% 9.27/3.27  ----------------------
% 9.27/3.27  #Ref     : 0
% 9.27/3.27  #Sup     : 2514
% 9.27/3.27  #Fact    : 0
% 9.27/3.27  #Define  : 0
% 9.27/3.27  #Split   : 24
% 9.27/3.27  #Chain   : 0
% 9.27/3.27  #Close   : 0
% 9.27/3.27  
% 9.27/3.27  Ordering : KBO
% 9.27/3.27  
% 9.27/3.27  Simplification rules
% 9.27/3.27  ----------------------
% 9.27/3.27  #Subsume      : 1475
% 9.27/3.27  #Demod        : 839
% 9.27/3.27  #Tautology    : 112
% 9.27/3.27  #SimpNegUnit  : 10
% 9.27/3.27  #BackRed      : 0
% 9.27/3.27  
% 9.27/3.27  #Partial instantiations: 0
% 9.27/3.27  #Strategies tried      : 1
% 9.27/3.27  
% 9.27/3.27  Timing (in seconds)
% 9.27/3.27  ----------------------
% 9.27/3.27  Preprocessing        : 0.28
% 9.27/3.27  Parsing              : 0.16
% 9.27/3.27  CNF conversion       : 0.02
% 9.27/3.27  Main loop            : 2.22
% 9.27/3.27  Inferencing          : 0.54
% 9.27/3.27  Reduction            : 0.57
% 9.27/3.27  Demodulation         : 0.37
% 9.27/3.27  BG Simplification    : 0.04
% 9.27/3.27  Subsumption          : 0.95
% 9.27/3.27  Abstraction          : 0.07
% 9.27/3.27  MUC search           : 0.00
% 9.27/3.27  Cooper               : 0.00
% 9.27/3.27  Total                : 2.53
% 9.27/3.27  Index Insertion      : 0.00
% 9.27/3.27  Index Deletion       : 0.00
% 9.27/3.27  Index Matching       : 0.00
% 9.27/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
