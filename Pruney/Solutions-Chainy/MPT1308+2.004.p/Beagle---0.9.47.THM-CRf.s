%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   58 (  70 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 189 expanded)
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

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_68,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_tops_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

tff(c_60,plain,(
    ~ v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_42,plain,(
    ! [A_10,B_19] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_10),B_19),u1_pre_topc(A_10))
      | ~ r1_tarski(B_19,u1_pre_topc(A_10))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ v2_pre_topc(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k5_setfam_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    ! [B_45,A_46] :
      ( v3_pre_topc(B_45,A_46)
      | ~ r2_hidden(B_45,u1_pre_topc(A_46))
      | ~ m1_subset_1(B_45,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_242,plain,(
    ! [A_83,B_84] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_83),B_84),A_83)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(A_83),B_84),u1_pre_topc(A_83))
      | ~ l1_pre_topc(A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83)))) ) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_253,plain,(
    ! [A_86,B_87] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_86),B_87),A_86)
      | ~ r1_tarski(B_87,u1_pre_topc(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_86))))
      | ~ v2_pre_topc(A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(resolution,[status(thm)],[c_42,c_242])).

tff(c_267,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_253])).

tff(c_275,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_267])).

tff(c_276,plain,(
    ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_275])).

tff(c_62,plain,(
    v1_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    ! [A_27] :
      ( m1_subset_1(u1_pre_topc(A_27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27))))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

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

tff(c_278,plain,(
    ! [C_89,A_90,B_91] :
      ( v3_pre_topc(C_89,A_90)
      | ~ r2_hidden(C_89,B_91)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ v1_tops_2(B_91,A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_90))))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_514,plain,(
    ! [A_151,B_152,C_153,A_154] :
      ( v3_pre_topc('#skF_1'(A_151,B_152,C_153),A_154)
      | ~ m1_subset_1('#skF_1'(A_151,B_152,C_153),k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ v1_tops_2(B_152,A_154)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_154))))
      | ~ l1_pre_topc(A_154)
      | r1_tarski(B_152,C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(A_151))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_151)) ) ),
    inference(resolution,[status(thm)],[c_4,c_278])).

tff(c_526,plain,(
    ! [A_157,B_158,C_159] :
      ( v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_157)),B_158,C_159),A_157)
      | ~ v1_tops_2(B_158,A_157)
      | ~ l1_pre_topc(A_157)
      | r1_tarski(B_158,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_157))))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_157)))) ) ),
    inference(resolution,[status(thm)],[c_6,c_514])).

tff(c_106,plain,(
    ! [A_58,B_59,C_60] :
      ( m1_subset_1('#skF_1'(A_58,B_59,C_60),A_58)
      | r1_tarski(B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    ! [B_26,A_24] :
      ( r2_hidden(B_26,u1_pre_topc(A_24))
      | ~ v3_pre_topc(B_26,A_24)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_494,plain,(
    ! [A_143,B_144,C_145] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_143)),B_144,C_145),u1_pre_topc(A_143))
      | ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_143)),B_144,C_145),A_143)
      | ~ l1_pre_topc(A_143)
      | r1_tarski(B_144,C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143))))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))) ) ),
    inference(resolution,[status(thm)],[c_106,c_48])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_502,plain,(
    ! [A_143,B_144] :
      ( ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_143)),B_144,u1_pre_topc(A_143)),A_143)
      | ~ l1_pre_topc(A_143)
      | r1_tarski(B_144,u1_pre_topc(A_143))
      | ~ m1_subset_1(u1_pre_topc(A_143),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143))))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))) ) ),
    inference(resolution,[status(thm)],[c_494,c_2])).

tff(c_532,plain,(
    ! [B_160,A_161] :
      ( ~ v1_tops_2(B_160,A_161)
      | ~ l1_pre_topc(A_161)
      | r1_tarski(B_160,u1_pre_topc(A_161))
      | ~ m1_subset_1(u1_pre_topc(A_161),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161))))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))) ) ),
    inference(resolution,[status(thm)],[c_526,c_502])).

tff(c_536,plain,(
    ! [B_162,A_163] :
      ( ~ v1_tops_2(B_162,A_163)
      | r1_tarski(B_162,u1_pre_topc(A_163))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_163))))
      | ~ l1_pre_topc(A_163) ) ),
    inference(resolution,[status(thm)],[c_50,c_532])).

tff(c_562,plain,
    ( ~ v1_tops_2('#skF_7','#skF_6')
    | r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_536])).

tff(c_572,plain,(
    r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_562])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:08:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.53  
% 3.35/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.53  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_5
% 3.35/1.53  
% 3.35/1.53  %Foreground sorts:
% 3.35/1.53  
% 3.35/1.53  
% 3.35/1.53  %Background operators:
% 3.35/1.53  
% 3.35/1.53  
% 3.35/1.53  %Foreground operators:
% 3.35/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.35/1.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.35/1.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.35/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.35/1.53  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.35/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.53  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 3.35/1.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.35/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.53  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 3.35/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.53  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.35/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.35/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.35/1.53  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.35/1.53  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.35/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.53  
% 3.42/1.55  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v3_pre_topc(k5_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tops_2)).
% 3.42/1.55  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 3.42/1.55  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 3.42/1.55  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 3.42/1.55  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.42/1.55  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 3.42/1.55  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 3.42/1.55  tff(c_60, plain, (~v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.42/1.55  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.42/1.55  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.42/1.55  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.42/1.55  tff(c_42, plain, (![A_10, B_19]: (r2_hidden(k5_setfam_1(u1_struct_0(A_10), B_19), u1_pre_topc(A_10)) | ~r1_tarski(B_19, u1_pre_topc(A_10)) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~v2_pre_topc(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.55  tff(c_8, plain, (![A_8, B_9]: (m1_subset_1(k5_setfam_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.42/1.55  tff(c_78, plain, (![B_45, A_46]: (v3_pre_topc(B_45, A_46) | ~r2_hidden(B_45, u1_pre_topc(A_46)) | ~m1_subset_1(B_45, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.55  tff(c_242, plain, (![A_83, B_84]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_83), B_84), A_83) | ~r2_hidden(k5_setfam_1(u1_struct_0(A_83), B_84), u1_pre_topc(A_83)) | ~l1_pre_topc(A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_83)))))), inference(resolution, [status(thm)], [c_8, c_78])).
% 3.42/1.55  tff(c_253, plain, (![A_86, B_87]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_86), B_87), A_86) | ~r1_tarski(B_87, u1_pre_topc(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_86)))) | ~v2_pre_topc(A_86) | ~l1_pre_topc(A_86))), inference(resolution, [status(thm)], [c_42, c_242])).
% 3.42/1.55  tff(c_267, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_253])).
% 3.42/1.55  tff(c_275, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_267])).
% 3.42/1.55  tff(c_276, plain, (~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_275])).
% 3.42/1.55  tff(c_62, plain, (v1_tops_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.42/1.55  tff(c_50, plain, (![A_27]: (m1_subset_1(u1_pre_topc(A_27), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_27)))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.42/1.55  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.55  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.55  tff(c_278, plain, (![C_89, A_90, B_91]: (v3_pre_topc(C_89, A_90) | ~r2_hidden(C_89, B_91) | ~m1_subset_1(C_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~v1_tops_2(B_91, A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_90)))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.42/1.55  tff(c_514, plain, (![A_151, B_152, C_153, A_154]: (v3_pre_topc('#skF_1'(A_151, B_152, C_153), A_154) | ~m1_subset_1('#skF_1'(A_151, B_152, C_153), k1_zfmisc_1(u1_struct_0(A_154))) | ~v1_tops_2(B_152, A_154) | ~m1_subset_1(B_152, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_154)))) | ~l1_pre_topc(A_154) | r1_tarski(B_152, C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(A_151)) | ~m1_subset_1(B_152, k1_zfmisc_1(A_151)))), inference(resolution, [status(thm)], [c_4, c_278])).
% 3.42/1.55  tff(c_526, plain, (![A_157, B_158, C_159]: (v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_157)), B_158, C_159), A_157) | ~v1_tops_2(B_158, A_157) | ~l1_pre_topc(A_157) | r1_tarski(B_158, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_157)))) | ~m1_subset_1(B_158, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_157)))))), inference(resolution, [status(thm)], [c_6, c_514])).
% 3.42/1.55  tff(c_106, plain, (![A_58, B_59, C_60]: (m1_subset_1('#skF_1'(A_58, B_59, C_60), A_58) | r1_tarski(B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.55  tff(c_48, plain, (![B_26, A_24]: (r2_hidden(B_26, u1_pre_topc(A_24)) | ~v3_pre_topc(B_26, A_24) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.42/1.55  tff(c_494, plain, (![A_143, B_144, C_145]: (r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_143)), B_144, C_145), u1_pre_topc(A_143)) | ~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_143)), B_144, C_145), A_143) | ~l1_pre_topc(A_143) | r1_tarski(B_144, C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))) | ~m1_subset_1(B_144, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))))), inference(resolution, [status(thm)], [c_106, c_48])).
% 3.42/1.55  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.55  tff(c_502, plain, (![A_143, B_144]: (~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_143)), B_144, u1_pre_topc(A_143)), A_143) | ~l1_pre_topc(A_143) | r1_tarski(B_144, u1_pre_topc(A_143)) | ~m1_subset_1(u1_pre_topc(A_143), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))) | ~m1_subset_1(B_144, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_143)))))), inference(resolution, [status(thm)], [c_494, c_2])).
% 3.42/1.55  tff(c_532, plain, (![B_160, A_161]: (~v1_tops_2(B_160, A_161) | ~l1_pre_topc(A_161) | r1_tarski(B_160, u1_pre_topc(A_161)) | ~m1_subset_1(u1_pre_topc(A_161), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))) | ~m1_subset_1(B_160, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_161)))))), inference(resolution, [status(thm)], [c_526, c_502])).
% 3.42/1.55  tff(c_536, plain, (![B_162, A_163]: (~v1_tops_2(B_162, A_163) | r1_tarski(B_162, u1_pre_topc(A_163)) | ~m1_subset_1(B_162, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_163)))) | ~l1_pre_topc(A_163))), inference(resolution, [status(thm)], [c_50, c_532])).
% 3.42/1.55  tff(c_562, plain, (~v1_tops_2('#skF_7', '#skF_6') | r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_536])).
% 3.42/1.55  tff(c_572, plain, (r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_562])).
% 3.42/1.55  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_572])).
% 3.42/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.42/1.55  
% 3.42/1.55  Inference rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Ref     : 0
% 3.42/1.55  #Sup     : 109
% 3.42/1.55  #Fact    : 0
% 3.42/1.55  #Define  : 0
% 3.42/1.55  #Split   : 0
% 3.42/1.55  #Chain   : 0
% 3.42/1.55  #Close   : 0
% 3.42/1.55  
% 3.42/1.55  Ordering : KBO
% 3.42/1.55  
% 3.42/1.55  Simplification rules
% 3.42/1.55  ----------------------
% 3.42/1.55  #Subsume      : 18
% 3.42/1.55  #Demod        : 8
% 3.42/1.55  #Tautology    : 27
% 3.42/1.55  #SimpNegUnit  : 2
% 3.42/1.55  #BackRed      : 0
% 3.42/1.55  
% 3.42/1.55  #Partial instantiations: 0
% 3.42/1.55  #Strategies tried      : 1
% 3.42/1.55  
% 3.42/1.55  Timing (in seconds)
% 3.42/1.55  ----------------------
% 3.42/1.55  Preprocessing        : 0.34
% 3.42/1.55  Parsing              : 0.19
% 3.42/1.55  CNF conversion       : 0.03
% 3.42/1.55  Main loop            : 0.41
% 3.42/1.55  Inferencing          : 0.18
% 3.42/1.55  Reduction            : 0.10
% 3.42/1.55  Demodulation         : 0.06
% 3.42/1.55  BG Simplification    : 0.02
% 3.42/1.55  Subsumption          : 0.09
% 3.42/1.55  Abstraction          : 0.01
% 3.42/1.55  MUC search           : 0.00
% 3.42/1.55  Cooper               : 0.00
% 3.42/1.55  Total                : 0.78
% 3.42/1.55  Index Insertion      : 0.00
% 3.42/1.55  Index Deletion       : 0.00
% 3.42/1.55  Index Matching       : 0.00
% 3.42/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
