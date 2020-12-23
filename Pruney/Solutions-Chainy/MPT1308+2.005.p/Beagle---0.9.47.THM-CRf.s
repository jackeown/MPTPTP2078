%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   59 (  73 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 197 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_97,axiom,(
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

tff(c_60,plain,(
    ~ v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_409,plain,(
    ! [A_111,B_112] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_111),B_112),u1_pre_topc(A_111))
      | ~ r1_tarski(B_112,u1_pre_topc(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111))))
      | ~ v2_pre_topc(A_111)
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [A_28] :
      ( m1_subset_1(u1_pre_topc(A_28),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28))))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_71,plain,(
    ! [A_42,C_43,B_44] :
      ( m1_subset_1(A_42,C_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(C_43))
      | ~ r2_hidden(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [A_42,A_28] :
      ( m1_subset_1(A_42,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ r2_hidden(A_42,u1_pre_topc(A_28))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_50,c_71])).

tff(c_95,plain,(
    ! [B_54,A_55] :
      ( v3_pre_topc(B_54,A_55)
      | ~ r2_hidden(B_54,u1_pre_topc(A_55))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_102,plain,(
    ! [A_42,A_28] :
      ( v3_pre_topc(A_42,A_28)
      | ~ r2_hidden(A_42,u1_pre_topc(A_28))
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_76,c_95])).

tff(c_430,plain,(
    ! [A_113,B_114] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_113),B_114),A_113)
      | ~ r1_tarski(B_114,u1_pre_topc(A_113))
      | ~ m1_subset_1(B_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113))))
      | ~ v2_pre_topc(A_113)
      | ~ l1_pre_topc(A_113) ) ),
    inference(resolution,[status(thm)],[c_409,c_102])).

tff(c_439,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_430])).

tff(c_445,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_439])).

tff(c_446,plain,(
    ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_445])).

tff(c_62,plain,(
    v1_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_581,plain,(
    ! [C_128,A_129,B_130] :
      ( v3_pre_topc(C_128,A_129)
      | ~ r2_hidden(C_128,B_130)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ v1_tops_2(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129))))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1504,plain,(
    ! [A_250,B_251,C_252,A_253] :
      ( v3_pre_topc('#skF_1'(A_250,B_251,C_252),A_253)
      | ~ m1_subset_1('#skF_1'(A_250,B_251,C_252),k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ v1_tops_2(B_251,A_253)
      | ~ m1_subset_1(B_251,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_253))))
      | ~ l1_pre_topc(A_253)
      | r1_tarski(B_251,C_252)
      | ~ m1_subset_1(C_252,k1_zfmisc_1(A_250))
      | ~ m1_subset_1(B_251,k1_zfmisc_1(A_250)) ) ),
    inference(resolution,[status(thm)],[c_4,c_581])).

tff(c_1532,plain,(
    ! [A_254,B_255,C_256] :
      ( v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_254)),B_255,C_256),A_254)
      | ~ v1_tops_2(B_255,A_254)
      | ~ l1_pre_topc(A_254)
      | r1_tarski(B_255,C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_254))))
      | ~ m1_subset_1(B_255,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_254)))) ) ),
    inference(resolution,[status(thm)],[c_6,c_1504])).

tff(c_225,plain,(
    ! [A_79,B_80,C_81] :
      ( m1_subset_1('#skF_1'(A_79,B_80,C_81),A_79)
      | r1_tarski(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [B_27,A_25] :
      ( r2_hidden(B_27,u1_pre_topc(A_25))
      | ~ v3_pre_topc(B_27,A_25)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1431,plain,(
    ! [A_234,B_235,C_236] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_234)),B_235,C_236),u1_pre_topc(A_234))
      | ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_234)),B_235,C_236),A_234)
      | ~ l1_pre_topc(A_234)
      | r1_tarski(B_235,C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234))))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))) ) ),
    inference(resolution,[status(thm)],[c_225,c_48])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1459,plain,(
    ! [A_234,B_235] :
      ( ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_234)),B_235,u1_pre_topc(A_234)),A_234)
      | ~ l1_pre_topc(A_234)
      | r1_tarski(B_235,u1_pre_topc(A_234))
      | ~ m1_subset_1(u1_pre_topc(A_234),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234))))
      | ~ m1_subset_1(B_235,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))) ) ),
    inference(resolution,[status(thm)],[c_1431,c_2])).

tff(c_1545,plain,(
    ! [B_257,A_258] :
      ( ~ v1_tops_2(B_257,A_258)
      | ~ l1_pre_topc(A_258)
      | r1_tarski(B_257,u1_pre_topc(A_258))
      | ~ m1_subset_1(u1_pre_topc(A_258),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_258))))
      | ~ m1_subset_1(B_257,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_258)))) ) ),
    inference(resolution,[status(thm)],[c_1532,c_1459])).

tff(c_1549,plain,(
    ! [B_259,A_260] :
      ( ~ v1_tops_2(B_259,A_260)
      | r1_tarski(B_259,u1_pre_topc(A_260))
      | ~ m1_subset_1(B_259,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_260))))
      | ~ l1_pre_topc(A_260) ) ),
    inference(resolution,[status(thm)],[c_50,c_1545])).

tff(c_1571,plain,
    ( ~ v1_tops_2('#skF_7','#skF_6')
    | r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1549])).

tff(c_1580,plain,(
    r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1571])).

tff(c_1582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_446,c_1580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.82  
% 4.62/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.82  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_5
% 4.62/1.82  
% 4.62/1.82  %Foreground sorts:
% 4.62/1.82  
% 4.62/1.82  
% 4.62/1.82  %Background operators:
% 4.62/1.82  
% 4.62/1.82  
% 4.62/1.82  %Foreground operators:
% 4.62/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.62/1.82  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.62/1.82  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.62/1.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.62/1.82  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.82  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.62/1.82  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.62/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.82  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.82  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.62/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.82  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.62/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.62/1.82  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.62/1.82  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.62/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.82  
% 4.62/1.84  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v3_pre_topc(k5_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tops_2)).
% 4.62/1.84  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 4.62/1.84  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.62/1.84  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 4.62/1.84  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.62/1.84  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 4.62/1.84  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 4.62/1.84  tff(c_60, plain, (~v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.62/1.84  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.62/1.84  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.62/1.84  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.62/1.84  tff(c_409, plain, (![A_111, B_112]: (r2_hidden(k5_setfam_1(u1_struct_0(A_111), B_112), u1_pre_topc(A_111)) | ~r1_tarski(B_112, u1_pre_topc(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_111)))) | ~v2_pre_topc(A_111) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.62/1.84  tff(c_50, plain, (![A_28]: (m1_subset_1(u1_pre_topc(A_28), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_28)))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.62/1.84  tff(c_71, plain, (![A_42, C_43, B_44]: (m1_subset_1(A_42, C_43) | ~m1_subset_1(B_44, k1_zfmisc_1(C_43)) | ~r2_hidden(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.84  tff(c_76, plain, (![A_42, A_28]: (m1_subset_1(A_42, k1_zfmisc_1(u1_struct_0(A_28))) | ~r2_hidden(A_42, u1_pre_topc(A_28)) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_50, c_71])).
% 4.62/1.84  tff(c_95, plain, (![B_54, A_55]: (v3_pre_topc(B_54, A_55) | ~r2_hidden(B_54, u1_pre_topc(A_55)) | ~m1_subset_1(B_54, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.62/1.84  tff(c_102, plain, (![A_42, A_28]: (v3_pre_topc(A_42, A_28) | ~r2_hidden(A_42, u1_pre_topc(A_28)) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_76, c_95])).
% 4.62/1.84  tff(c_430, plain, (![A_113, B_114]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_113), B_114), A_113) | ~r1_tarski(B_114, u1_pre_topc(A_113)) | ~m1_subset_1(B_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_113)))) | ~v2_pre_topc(A_113) | ~l1_pre_topc(A_113))), inference(resolution, [status(thm)], [c_409, c_102])).
% 4.62/1.84  tff(c_439, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_430])).
% 4.62/1.84  tff(c_445, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_439])).
% 4.62/1.84  tff(c_446, plain, (~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_445])).
% 4.62/1.84  tff(c_62, plain, (v1_tops_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.62/1.84  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.84  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.84  tff(c_581, plain, (![C_128, A_129, B_130]: (v3_pre_topc(C_128, A_129) | ~r2_hidden(C_128, B_130) | ~m1_subset_1(C_128, k1_zfmisc_1(u1_struct_0(A_129))) | ~v1_tops_2(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_129)))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.62/1.84  tff(c_1504, plain, (![A_250, B_251, C_252, A_253]: (v3_pre_topc('#skF_1'(A_250, B_251, C_252), A_253) | ~m1_subset_1('#skF_1'(A_250, B_251, C_252), k1_zfmisc_1(u1_struct_0(A_253))) | ~v1_tops_2(B_251, A_253) | ~m1_subset_1(B_251, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_253)))) | ~l1_pre_topc(A_253) | r1_tarski(B_251, C_252) | ~m1_subset_1(C_252, k1_zfmisc_1(A_250)) | ~m1_subset_1(B_251, k1_zfmisc_1(A_250)))), inference(resolution, [status(thm)], [c_4, c_581])).
% 4.62/1.84  tff(c_1532, plain, (![A_254, B_255, C_256]: (v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_254)), B_255, C_256), A_254) | ~v1_tops_2(B_255, A_254) | ~l1_pre_topc(A_254) | r1_tarski(B_255, C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_254)))) | ~m1_subset_1(B_255, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_254)))))), inference(resolution, [status(thm)], [c_6, c_1504])).
% 4.62/1.84  tff(c_225, plain, (![A_79, B_80, C_81]: (m1_subset_1('#skF_1'(A_79, B_80, C_81), A_79) | r1_tarski(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.84  tff(c_48, plain, (![B_27, A_25]: (r2_hidden(B_27, u1_pre_topc(A_25)) | ~v3_pre_topc(B_27, A_25) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.62/1.84  tff(c_1431, plain, (![A_234, B_235, C_236]: (r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_234)), B_235, C_236), u1_pre_topc(A_234)) | ~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_234)), B_235, C_236), A_234) | ~l1_pre_topc(A_234) | r1_tarski(B_235, C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))) | ~m1_subset_1(B_235, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))))), inference(resolution, [status(thm)], [c_225, c_48])).
% 4.62/1.84  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.84  tff(c_1459, plain, (![A_234, B_235]: (~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_234)), B_235, u1_pre_topc(A_234)), A_234) | ~l1_pre_topc(A_234) | r1_tarski(B_235, u1_pre_topc(A_234)) | ~m1_subset_1(u1_pre_topc(A_234), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))) | ~m1_subset_1(B_235, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))))), inference(resolution, [status(thm)], [c_1431, c_2])).
% 4.62/1.84  tff(c_1545, plain, (![B_257, A_258]: (~v1_tops_2(B_257, A_258) | ~l1_pre_topc(A_258) | r1_tarski(B_257, u1_pre_topc(A_258)) | ~m1_subset_1(u1_pre_topc(A_258), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_258)))) | ~m1_subset_1(B_257, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_258)))))), inference(resolution, [status(thm)], [c_1532, c_1459])).
% 4.62/1.84  tff(c_1549, plain, (![B_259, A_260]: (~v1_tops_2(B_259, A_260) | r1_tarski(B_259, u1_pre_topc(A_260)) | ~m1_subset_1(B_259, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_260)))) | ~l1_pre_topc(A_260))), inference(resolution, [status(thm)], [c_50, c_1545])).
% 4.62/1.84  tff(c_1571, plain, (~v1_tops_2('#skF_7', '#skF_6') | r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_1549])).
% 4.62/1.84  tff(c_1580, plain, (r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1571])).
% 4.62/1.84  tff(c_1582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_446, c_1580])).
% 4.62/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.62/1.84  
% 4.62/1.84  Inference rules
% 4.62/1.84  ----------------------
% 4.62/1.84  #Ref     : 0
% 4.62/1.84  #Sup     : 315
% 4.62/1.84  #Fact    : 4
% 4.62/1.84  #Define  : 0
% 4.62/1.84  #Split   : 5
% 4.62/1.84  #Chain   : 0
% 4.62/1.84  #Close   : 0
% 4.62/1.84  
% 4.62/1.84  Ordering : KBO
% 4.62/1.84  
% 4.62/1.84  Simplification rules
% 4.62/1.84  ----------------------
% 4.62/1.84  #Subsume      : 60
% 4.62/1.84  #Demod        : 96
% 4.62/1.84  #Tautology    : 56
% 4.62/1.84  #SimpNegUnit  : 3
% 4.62/1.84  #BackRed      : 0
% 4.62/1.84  
% 4.62/1.84  #Partial instantiations: 0
% 4.62/1.84  #Strategies tried      : 1
% 4.62/1.84  
% 4.62/1.84  Timing (in seconds)
% 4.62/1.84  ----------------------
% 4.62/1.84  Preprocessing        : 0.30
% 4.62/1.84  Parsing              : 0.16
% 4.62/1.84  CNF conversion       : 0.02
% 4.62/1.84  Main loop            : 0.74
% 4.62/1.84  Inferencing          : 0.27
% 4.62/1.84  Reduction            : 0.17
% 4.62/1.84  Demodulation         : 0.10
% 4.62/1.84  BG Simplification    : 0.03
% 4.62/1.84  Subsumption          : 0.22
% 4.62/1.84  Abstraction          : 0.03
% 4.62/1.84  MUC search           : 0.00
% 4.62/1.84  Cooper               : 0.00
% 4.62/1.84  Total                : 1.07
% 4.62/1.84  Index Insertion      : 0.00
% 4.62/1.84  Index Deletion       : 0.00
% 4.62/1.84  Index Matching       : 0.00
% 4.62/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
