%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:11 EST 2020

% Result     : Theorem 18.21s
% Output     : CNFRefutation 18.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 101 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 211 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v2_tex_2(B,A)
                    | v2_tex_2(C,A) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( r1_tarski(C,B)
                  & v2_tex_2(B,A) )
               => v2_tex_2(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11051,plain,(
    ! [A_260,B_261] :
      ( r1_tarski(A_260,B_261)
      | ~ m1_subset_1(A_260,k1_zfmisc_1(B_261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_11058,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_11051])).

tff(c_30,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_67,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_67])).

tff(c_24,plain,
    ( v2_tex_2('#skF_3','#skF_1')
    | v2_tex_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    v2_tex_2('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(k4_xboole_0(A_3,C_5),B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    ! [C_62,A_63,B_64] :
      ( v2_tex_2(C_62,A_63)
      | ~ v2_tex_2(B_64,A_63)
      | ~ r1_tarski(C_62,B_64)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_338,plain,(
    ! [A_79,B_80,A_81] :
      ( v2_tex_2(k4_xboole_0(A_79,B_80),A_81)
      | ~ v2_tex_2(A_79,A_81)
      | ~ m1_subset_1(k4_xboole_0(A_79,B_80),k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ m1_subset_1(A_79,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_2327,plain,(
    ! [A_149,B_150,A_151] :
      ( v2_tex_2(k4_xboole_0(A_149,B_150),A_151)
      | ~ v2_tex_2(A_149,A_151)
      | ~ m1_subset_1(A_149,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151)
      | ~ r1_tarski(k4_xboole_0(A_149,B_150),u1_struct_0(A_151)) ) ),
    inference(resolution,[status(thm)],[c_18,c_338])).

tff(c_10900,plain,(
    ! [A_253,C_254,A_255] :
      ( v2_tex_2(k4_xboole_0(A_253,C_254),A_255)
      | ~ v2_tex_2(A_253,A_255)
      | ~ m1_subset_1(A_253,k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ l1_pre_topc(A_255)
      | ~ r1_tarski(A_253,u1_struct_0(A_255)) ) ),
    inference(resolution,[status(thm)],[c_4,c_2327])).

tff(c_10907,plain,(
    ! [C_254] :
      ( v2_tex_2(k4_xboole_0('#skF_2',C_254),'#skF_1')
      | ~ v2_tex_2('#skF_2','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_10900])).

tff(c_10915,plain,(
    ! [C_256] : v2_tex_2(k4_xboole_0('#skF_2',C_256),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_30,c_32,c_10907])).

tff(c_10964,plain,(
    ! [B_257] : v2_tex_2(k3_xboole_0('#skF_2',B_257),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_10915])).

tff(c_11000,plain,(
    ! [B_2] : v2_tex_2(k3_xboole_0(B_2,'#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10964])).

tff(c_137,plain,(
    ! [A_51,B_52,C_53] :
      ( k9_subset_1(A_51,B_52,C_53) = k3_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,(
    ! [B_52] : k9_subset_1(u1_struct_0('#skF_1'),B_52,'#skF_3') = k3_xboole_0(B_52,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_137])).

tff(c_22,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_163,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_22])).

tff(c_164,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_11015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11000,c_164])).

tff(c_11016,plain,(
    v2_tex_2('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_11159,plain,(
    ! [C_285,A_286,B_287] :
      ( v2_tex_2(C_285,A_286)
      | ~ v2_tex_2(B_287,A_286)
      | ~ r1_tarski(C_285,B_287)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_11244,plain,(
    ! [A_296,B_297,A_298] :
      ( v2_tex_2(k4_xboole_0(A_296,B_297),A_298)
      | ~ v2_tex_2(A_296,A_298)
      | ~ m1_subset_1(k4_xboole_0(A_296,B_297),k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ m1_subset_1(A_296,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ l1_pre_topc(A_298) ) ),
    inference(resolution,[status(thm)],[c_6,c_11159])).

tff(c_13234,plain,(
    ! [A_373,B_374,A_375] :
      ( v2_tex_2(k4_xboole_0(A_373,B_374),A_375)
      | ~ v2_tex_2(A_373,A_375)
      | ~ m1_subset_1(A_373,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375)
      | ~ r1_tarski(k4_xboole_0(A_373,B_374),u1_struct_0(A_375)) ) ),
    inference(resolution,[status(thm)],[c_18,c_11244])).

tff(c_33766,plain,(
    ! [A_521,C_522,A_523] :
      ( v2_tex_2(k4_xboole_0(A_521,C_522),A_523)
      | ~ v2_tex_2(A_521,A_523)
      | ~ m1_subset_1(A_521,k1_zfmisc_1(u1_struct_0(A_523)))
      | ~ l1_pre_topc(A_523)
      | ~ r1_tarski(A_521,u1_struct_0(A_523)) ) ),
    inference(resolution,[status(thm)],[c_4,c_13234])).

tff(c_33771,plain,(
    ! [C_522] :
      ( v2_tex_2(k4_xboole_0('#skF_3',C_522),'#skF_1')
      | ~ v2_tex_2('#skF_3','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_26,c_33766])).

tff(c_33781,plain,(
    ! [C_524] : v2_tex_2(k4_xboole_0('#skF_3',C_524),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11058,c_30,c_11016,c_33771])).

tff(c_33829,plain,(
    ! [B_9] : v2_tex_2(k3_xboole_0('#skF_3',B_9),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_33781])).

tff(c_11129,plain,(
    ! [A_280,B_281,C_282] :
      ( k9_subset_1(A_280,B_281,C_282) = k3_xboole_0(B_281,C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(A_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11137,plain,(
    ! [B_281] : k9_subset_1(u1_struct_0('#skF_1'),B_281,'#skF_3') = k3_xboole_0(B_281,'#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_11129])).

tff(c_11139,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11137,c_22])).

tff(c_11140,plain,(
    ~ v2_tex_2(k3_xboole_0('#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_11139])).

tff(c_33832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33829,c_11140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.21/9.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.21/9.76  
% 18.21/9.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.21/9.76  %$ v2_tex_2 > r1_tarski > m1_subset_1 > l1_pre_topc > k2_enumset1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 18.21/9.76  
% 18.21/9.76  %Foreground sorts:
% 18.21/9.76  
% 18.21/9.76  
% 18.21/9.76  %Background operators:
% 18.21/9.76  
% 18.21/9.76  
% 18.21/9.76  %Foreground operators:
% 18.21/9.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.21/9.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.21/9.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.21/9.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.21/9.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.21/9.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.21/9.76  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 18.21/9.76  tff('#skF_2', type, '#skF_2': $i).
% 18.21/9.76  tff('#skF_3', type, '#skF_3': $i).
% 18.21/9.76  tff('#skF_1', type, '#skF_1': $i).
% 18.21/9.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.21/9.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.21/9.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.21/9.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.21/9.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.21/9.76  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 18.21/9.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.21/9.76  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.21/9.76  
% 18.21/9.77  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.21/9.77  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(B, A) | v2_tex_2(C, A)) => v2_tex_2(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tex_2)).
% 18.21/9.77  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 18.21/9.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.21/9.77  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 18.21/9.77  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 18.21/9.77  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r1_tarski(C, B) & v2_tex_2(B, A)) => v2_tex_2(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tex_2)).
% 18.21/9.77  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 18.21/9.77  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.21/9.77  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.21/9.77  tff(c_11051, plain, (![A_260, B_261]: (r1_tarski(A_260, B_261) | ~m1_subset_1(A_260, k1_zfmisc_1(B_261)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.21/9.77  tff(c_11058, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_11051])).
% 18.21/9.77  tff(c_30, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.21/9.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.21/9.77  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.21/9.77  tff(c_67, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | ~m1_subset_1(A_36, k1_zfmisc_1(B_37)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.21/9.77  tff(c_79, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_67])).
% 18.21/9.77  tff(c_24, plain, (v2_tex_2('#skF_3', '#skF_1') | v2_tex_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.21/9.77  tff(c_32, plain, (v2_tex_2('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 18.21/9.77  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(k4_xboole_0(A_3, C_5), B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.21/9.78  tff(c_18, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.21/9.78  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 18.21/9.78  tff(c_181, plain, (![C_62, A_63, B_64]: (v2_tex_2(C_62, A_63) | ~v2_tex_2(B_64, A_63) | ~r1_tarski(C_62, B_64) | ~m1_subset_1(C_62, k1_zfmisc_1(u1_struct_0(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_61])).
% 18.21/9.78  tff(c_338, plain, (![A_79, B_80, A_81]: (v2_tex_2(k4_xboole_0(A_79, B_80), A_81) | ~v2_tex_2(A_79, A_81) | ~m1_subset_1(k4_xboole_0(A_79, B_80), k1_zfmisc_1(u1_struct_0(A_81))) | ~m1_subset_1(A_79, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(resolution, [status(thm)], [c_6, c_181])).
% 18.21/9.78  tff(c_2327, plain, (![A_149, B_150, A_151]: (v2_tex_2(k4_xboole_0(A_149, B_150), A_151) | ~v2_tex_2(A_149, A_151) | ~m1_subset_1(A_149, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151) | ~r1_tarski(k4_xboole_0(A_149, B_150), u1_struct_0(A_151)))), inference(resolution, [status(thm)], [c_18, c_338])).
% 18.21/9.78  tff(c_10900, plain, (![A_253, C_254, A_255]: (v2_tex_2(k4_xboole_0(A_253, C_254), A_255) | ~v2_tex_2(A_253, A_255) | ~m1_subset_1(A_253, k1_zfmisc_1(u1_struct_0(A_255))) | ~l1_pre_topc(A_255) | ~r1_tarski(A_253, u1_struct_0(A_255)))), inference(resolution, [status(thm)], [c_4, c_2327])).
% 18.21/9.78  tff(c_10907, plain, (![C_254]: (v2_tex_2(k4_xboole_0('#skF_2', C_254), '#skF_1') | ~v2_tex_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_2', u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_10900])).
% 18.21/9.78  tff(c_10915, plain, (![C_256]: (v2_tex_2(k4_xboole_0('#skF_2', C_256), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_30, c_32, c_10907])).
% 18.21/9.78  tff(c_10964, plain, (![B_257]: (v2_tex_2(k3_xboole_0('#skF_2', B_257), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_10915])).
% 18.21/9.78  tff(c_11000, plain, (![B_2]: (v2_tex_2(k3_xboole_0(B_2, '#skF_2'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10964])).
% 18.21/9.78  tff(c_137, plain, (![A_51, B_52, C_53]: (k9_subset_1(A_51, B_52, C_53)=k3_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.21/9.78  tff(c_145, plain, (![B_52]: (k9_subset_1(u1_struct_0('#skF_1'), B_52, '#skF_3')=k3_xboole_0(B_52, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_137])).
% 18.21/9.78  tff(c_22, plain, (~v2_tex_2(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 18.21/9.78  tff(c_163, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_22])).
% 18.21/9.78  tff(c_164, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_163])).
% 18.21/9.78  tff(c_11015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11000, c_164])).
% 18.21/9.78  tff(c_11016, plain, (v2_tex_2('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 18.21/9.78  tff(c_11159, plain, (![C_285, A_286, B_287]: (v2_tex_2(C_285, A_286) | ~v2_tex_2(B_287, A_286) | ~r1_tarski(C_285, B_287) | ~m1_subset_1(C_285, k1_zfmisc_1(u1_struct_0(A_286))) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_61])).
% 18.21/9.78  tff(c_11244, plain, (![A_296, B_297, A_298]: (v2_tex_2(k4_xboole_0(A_296, B_297), A_298) | ~v2_tex_2(A_296, A_298) | ~m1_subset_1(k4_xboole_0(A_296, B_297), k1_zfmisc_1(u1_struct_0(A_298))) | ~m1_subset_1(A_296, k1_zfmisc_1(u1_struct_0(A_298))) | ~l1_pre_topc(A_298))), inference(resolution, [status(thm)], [c_6, c_11159])).
% 18.21/9.78  tff(c_13234, plain, (![A_373, B_374, A_375]: (v2_tex_2(k4_xboole_0(A_373, B_374), A_375) | ~v2_tex_2(A_373, A_375) | ~m1_subset_1(A_373, k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375) | ~r1_tarski(k4_xboole_0(A_373, B_374), u1_struct_0(A_375)))), inference(resolution, [status(thm)], [c_18, c_11244])).
% 18.21/9.78  tff(c_33766, plain, (![A_521, C_522, A_523]: (v2_tex_2(k4_xboole_0(A_521, C_522), A_523) | ~v2_tex_2(A_521, A_523) | ~m1_subset_1(A_521, k1_zfmisc_1(u1_struct_0(A_523))) | ~l1_pre_topc(A_523) | ~r1_tarski(A_521, u1_struct_0(A_523)))), inference(resolution, [status(thm)], [c_4, c_13234])).
% 18.21/9.78  tff(c_33771, plain, (![C_522]: (v2_tex_2(k4_xboole_0('#skF_3', C_522), '#skF_1') | ~v2_tex_2('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~r1_tarski('#skF_3', u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_26, c_33766])).
% 18.21/9.78  tff(c_33781, plain, (![C_524]: (v2_tex_2(k4_xboole_0('#skF_3', C_524), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11058, c_30, c_11016, c_33771])).
% 18.21/9.78  tff(c_33829, plain, (![B_9]: (v2_tex_2(k3_xboole_0('#skF_3', B_9), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_33781])).
% 18.21/9.78  tff(c_11129, plain, (![A_280, B_281, C_282]: (k9_subset_1(A_280, B_281, C_282)=k3_xboole_0(B_281, C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(A_280)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.21/9.78  tff(c_11137, plain, (![B_281]: (k9_subset_1(u1_struct_0('#skF_1'), B_281, '#skF_3')=k3_xboole_0(B_281, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_11129])).
% 18.21/9.78  tff(c_11139, plain, (~v2_tex_2(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11137, c_22])).
% 18.21/9.78  tff(c_11140, plain, (~v2_tex_2(k3_xboole_0('#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_11139])).
% 18.21/9.78  tff(c_33832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33829, c_11140])).
% 18.21/9.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.21/9.78  
% 18.21/9.78  Inference rules
% 18.21/9.78  ----------------------
% 18.21/9.78  #Ref     : 0
% 18.21/9.78  #Sup     : 9505
% 18.21/9.78  #Fact    : 0
% 18.21/9.78  #Define  : 0
% 18.21/9.78  #Split   : 4
% 18.21/9.78  #Chain   : 0
% 18.21/9.78  #Close   : 0
% 18.21/9.78  
% 18.21/9.78  Ordering : KBO
% 18.21/9.78  
% 18.21/9.78  Simplification rules
% 18.21/9.78  ----------------------
% 18.21/9.78  #Subsume      : 1049
% 18.21/9.78  #Demod        : 2294
% 18.21/9.78  #Tautology    : 1540
% 18.21/9.78  #SimpNegUnit  : 0
% 18.21/9.78  #BackRed      : 4
% 18.21/9.78  
% 18.21/9.78  #Partial instantiations: 0
% 18.21/9.78  #Strategies tried      : 1
% 18.21/9.78  
% 18.21/9.78  Timing (in seconds)
% 18.21/9.78  ----------------------
% 18.21/9.78  Preprocessing        : 0.30
% 18.21/9.78  Parsing              : 0.17
% 18.21/9.78  CNF conversion       : 0.02
% 18.21/9.78  Main loop            : 8.70
% 18.21/9.78  Inferencing          : 1.38
% 18.21/9.78  Reduction            : 5.97
% 18.21/9.78  Demodulation         : 5.71
% 18.21/9.78  BG Simplification    : 0.25
% 18.21/9.78  Subsumption          : 0.85
% 18.21/9.78  Abstraction          : 0.31
% 18.21/9.78  MUC search           : 0.00
% 18.21/9.78  Cooper               : 0.00
% 18.21/9.78  Total                : 9.04
% 18.21/9.78  Index Insertion      : 0.00
% 18.21/9.78  Index Deletion       : 0.00
% 18.21/9.78  Index Matching       : 0.00
% 18.21/9.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
