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
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.18s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 128 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  135 ( 352 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tops_2)).

tff(f_67,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_90,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_44,plain,(
    ! [A_11,B_20] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_11),B_20),u1_pre_topc(A_11))
      | ~ r1_tarski(B_20,u1_pre_topc(A_11))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ v2_pre_topc(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k5_setfam_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_167,plain,(
    ! [B_72,A_73] :
      ( v3_pre_topc(B_72,A_73)
      | ~ r2_hidden(B_72,u1_pre_topc(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_444,plain,(
    ! [A_134,B_135] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_134),B_135),A_134)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(A_134),B_135),u1_pre_topc(A_134))
      | ~ l1_pre_topc(A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_134)))) ) ),
    inference(resolution,[status(thm)],[c_8,c_167])).

tff(c_456,plain,(
    ! [A_136,B_137] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_136),B_137),A_136)
      | ~ r1_tarski(B_137,u1_pre_topc(A_136))
      | ~ m1_subset_1(B_137,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_136))))
      | ~ v2_pre_topc(A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_44,c_444])).

tff(c_468,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_456])).

tff(c_475,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_468])).

tff(c_476,plain,(
    ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_475])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_78,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_1,B_2,B_46] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_46)
      | ~ r1_tarski(A_1,B_46)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_62,plain,(
    v1_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_85,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_48,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_85])).

tff(c_514,plain,(
    ! [C_146,A_147,B_148] :
      ( v3_pre_topc(C_146,A_147)
      | ~ r2_hidden(C_146,B_148)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(u1_struct_0(A_147)))
      | ~ v1_tops_2(B_148,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_147))))
      | ~ l1_pre_topc(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1232,plain,(
    ! [A_232,B_233,A_234] :
      ( v3_pre_topc('#skF_1'(A_232,B_233),A_234)
      | ~ m1_subset_1('#skF_1'(A_232,B_233),k1_zfmisc_1(u1_struct_0(A_234)))
      | ~ v1_tops_2(A_232,A_234)
      | ~ m1_subset_1(A_232,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234))))
      | ~ l1_pre_topc(A_234)
      | r1_tarski(A_232,B_233) ) ),
    inference(resolution,[status(thm)],[c_6,c_514])).

tff(c_1252,plain,(
    ! [A_232,B_233] :
      ( v3_pre_topc('#skF_1'(A_232,B_233),'#skF_6')
      | ~ v1_tops_2(A_232,'#skF_6')
      | ~ m1_subset_1(A_232,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
      | ~ l1_pre_topc('#skF_6')
      | r1_tarski(A_232,B_233)
      | ~ r2_hidden('#skF_1'(A_232,B_233),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_88,c_1232])).

tff(c_1261,plain,(
    ! [A_237,B_238] :
      ( v3_pre_topc('#skF_1'(A_237,B_238),'#skF_6')
      | ~ v1_tops_2(A_237,'#skF_6')
      | ~ m1_subset_1(A_237,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
      | r1_tarski(A_237,B_238)
      | ~ r2_hidden('#skF_1'(A_237,B_238),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1252])).

tff(c_1284,plain,(
    ! [B_238] :
      ( v3_pre_topc('#skF_1'('#skF_7',B_238),'#skF_6')
      | ~ v1_tops_2('#skF_7','#skF_6')
      | r1_tarski('#skF_7',B_238)
      | ~ r2_hidden('#skF_1'('#skF_7',B_238),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_1261])).

tff(c_1303,plain,(
    ! [B_239] :
      ( v3_pre_topc('#skF_1'('#skF_7',B_239),'#skF_6')
      | r1_tarski('#skF_7',B_239)
      | ~ r2_hidden('#skF_1'('#skF_7',B_239),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1284])).

tff(c_116,plain,(
    ! [B_59,A_60] :
      ( r2_hidden(B_59,u1_pre_topc(A_60))
      | ~ v3_pre_topc(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_123,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc(A_48,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r2_hidden(A_48,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_88,c_116])).

tff(c_128,plain,(
    ! [A_61] :
      ( r2_hidden(A_61,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc(A_61,'#skF_6')
      | ~ r2_hidden(A_61,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_139,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc('#skF_1'(A_1,u1_pre_topc('#skF_6')),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1,u1_pre_topc('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_128,c_4])).

tff(c_1307,plain,
    ( r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_7',u1_pre_topc('#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1303,c_139])).

tff(c_1310,plain,(
    ~ r2_hidden('#skF_1'('#skF_7',u1_pre_topc('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_476,c_1307])).

tff(c_1313,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_1310])).

tff(c_1319,plain,(
    r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1313])).

tff(c_1321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_476,c_1319])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.68  
% 4.18/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.68  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5
% 4.18/1.68  
% 4.18/1.68  %Foreground sorts:
% 4.18/1.68  
% 4.18/1.68  
% 4.18/1.68  %Background operators:
% 4.18/1.68  
% 4.18/1.68  
% 4.18/1.68  %Foreground operators:
% 4.18/1.68  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.18/1.68  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.18/1.68  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.18/1.68  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.18/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.18/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.18/1.68  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.18/1.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.18/1.68  tff('#skF_7', type, '#skF_7': $i).
% 4.18/1.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.18/1.68  tff('#skF_6', type, '#skF_6': $i).
% 4.18/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.18/1.68  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.18/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.18/1.68  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.18/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.18/1.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.18/1.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.18/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.18/1.68  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.18/1.68  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.18/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.18/1.68  
% 4.18/1.70  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v3_pre_topc(k5_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tops_2)).
% 4.18/1.70  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 4.18/1.70  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.18/1.70  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.18/1.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.18/1.70  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.18/1.70  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 4.18/1.70  tff(c_60, plain, (~v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.18/1.70  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.18/1.70  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.18/1.70  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.18/1.70  tff(c_44, plain, (![A_11, B_20]: (r2_hidden(k5_setfam_1(u1_struct_0(A_11), B_20), u1_pre_topc(A_11)) | ~r1_tarski(B_20, u1_pre_topc(A_11)) | ~m1_subset_1(B_20, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~v2_pre_topc(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.18/1.70  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k5_setfam_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.18/1.70  tff(c_167, plain, (![B_72, A_73]: (v3_pre_topc(B_72, A_73) | ~r2_hidden(B_72, u1_pre_topc(A_73)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.18/1.70  tff(c_444, plain, (![A_134, B_135]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_134), B_135), A_134) | ~r2_hidden(k5_setfam_1(u1_struct_0(A_134), B_135), u1_pre_topc(A_134)) | ~l1_pre_topc(A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_134)))))), inference(resolution, [status(thm)], [c_8, c_167])).
% 4.18/1.70  tff(c_456, plain, (![A_136, B_137]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_136), B_137), A_136) | ~r1_tarski(B_137, u1_pre_topc(A_136)) | ~m1_subset_1(B_137, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_136)))) | ~v2_pre_topc(A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_44, c_444])).
% 4.18/1.70  tff(c_468, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_456])).
% 4.18/1.70  tff(c_475, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_468])).
% 4.18/1.70  tff(c_476, plain, (~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_475])).
% 4.18/1.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.70  tff(c_70, plain, (![A_41, B_42]: (~r2_hidden('#skF_1'(A_41, B_42), B_42) | r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.70  tff(c_75, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_70])).
% 4.18/1.70  tff(c_78, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.70  tff(c_84, plain, (![A_1, B_2, B_46]: (r2_hidden('#skF_1'(A_1, B_2), B_46) | ~r1_tarski(A_1, B_46) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_78])).
% 4.18/1.70  tff(c_62, plain, (v1_tops_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.18/1.70  tff(c_85, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.18/1.70  tff(c_88, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(A_48, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_85])).
% 4.18/1.70  tff(c_514, plain, (![C_146, A_147, B_148]: (v3_pre_topc(C_146, A_147) | ~r2_hidden(C_146, B_148) | ~m1_subset_1(C_146, k1_zfmisc_1(u1_struct_0(A_147))) | ~v1_tops_2(B_148, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_147)))) | ~l1_pre_topc(A_147))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.18/1.70  tff(c_1232, plain, (![A_232, B_233, A_234]: (v3_pre_topc('#skF_1'(A_232, B_233), A_234) | ~m1_subset_1('#skF_1'(A_232, B_233), k1_zfmisc_1(u1_struct_0(A_234))) | ~v1_tops_2(A_232, A_234) | ~m1_subset_1(A_232, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_234)))) | ~l1_pre_topc(A_234) | r1_tarski(A_232, B_233))), inference(resolution, [status(thm)], [c_6, c_514])).
% 4.18/1.70  tff(c_1252, plain, (![A_232, B_233]: (v3_pre_topc('#skF_1'(A_232, B_233), '#skF_6') | ~v1_tops_2(A_232, '#skF_6') | ~m1_subset_1(A_232, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) | ~l1_pre_topc('#skF_6') | r1_tarski(A_232, B_233) | ~r2_hidden('#skF_1'(A_232, B_233), '#skF_7'))), inference(resolution, [status(thm)], [c_88, c_1232])).
% 4.18/1.70  tff(c_1261, plain, (![A_237, B_238]: (v3_pre_topc('#skF_1'(A_237, B_238), '#skF_6') | ~v1_tops_2(A_237, '#skF_6') | ~m1_subset_1(A_237, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) | r1_tarski(A_237, B_238) | ~r2_hidden('#skF_1'(A_237, B_238), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1252])).
% 4.18/1.70  tff(c_1284, plain, (![B_238]: (v3_pre_topc('#skF_1'('#skF_7', B_238), '#skF_6') | ~v1_tops_2('#skF_7', '#skF_6') | r1_tarski('#skF_7', B_238) | ~r2_hidden('#skF_1'('#skF_7', B_238), '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_1261])).
% 4.18/1.70  tff(c_1303, plain, (![B_239]: (v3_pre_topc('#skF_1'('#skF_7', B_239), '#skF_6') | r1_tarski('#skF_7', B_239) | ~r2_hidden('#skF_1'('#skF_7', B_239), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1284])).
% 4.18/1.70  tff(c_116, plain, (![B_59, A_60]: (r2_hidden(B_59, u1_pre_topc(A_60)) | ~v3_pre_topc(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.18/1.70  tff(c_123, plain, (![A_48]: (r2_hidden(A_48, u1_pre_topc('#skF_6')) | ~v3_pre_topc(A_48, '#skF_6') | ~l1_pre_topc('#skF_6') | ~r2_hidden(A_48, '#skF_7'))), inference(resolution, [status(thm)], [c_88, c_116])).
% 4.18/1.70  tff(c_128, plain, (![A_61]: (r2_hidden(A_61, u1_pre_topc('#skF_6')) | ~v3_pre_topc(A_61, '#skF_6') | ~r2_hidden(A_61, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_123])).
% 4.18/1.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.18/1.70  tff(c_139, plain, (![A_1]: (r1_tarski(A_1, u1_pre_topc('#skF_6')) | ~v3_pre_topc('#skF_1'(A_1, u1_pre_topc('#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'(A_1, u1_pre_topc('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_128, c_4])).
% 4.18/1.70  tff(c_1307, plain, (r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~r2_hidden('#skF_1'('#skF_7', u1_pre_topc('#skF_6')), '#skF_7')), inference(resolution, [status(thm)], [c_1303, c_139])).
% 4.18/1.70  tff(c_1310, plain, (~r2_hidden('#skF_1'('#skF_7', u1_pre_topc('#skF_6')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_476, c_476, c_1307])).
% 4.18/1.70  tff(c_1313, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_1310])).
% 4.18/1.70  tff(c_1319, plain, (r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1313])).
% 4.18/1.70  tff(c_1321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_476, c_1319])).
% 4.18/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.18/1.70  
% 4.18/1.70  Inference rules
% 4.18/1.70  ----------------------
% 4.18/1.70  #Ref     : 0
% 4.18/1.70  #Sup     : 257
% 4.18/1.70  #Fact    : 4
% 4.18/1.70  #Define  : 0
% 4.18/1.70  #Split   : 2
% 4.18/1.70  #Chain   : 0
% 4.18/1.70  #Close   : 0
% 4.18/1.70  
% 4.18/1.70  Ordering : KBO
% 4.18/1.70  
% 4.18/1.70  Simplification rules
% 4.18/1.70  ----------------------
% 4.18/1.70  #Subsume      : 24
% 4.18/1.70  #Demod        : 88
% 4.18/1.70  #Tautology    : 61
% 4.18/1.70  #SimpNegUnit  : 4
% 4.18/1.70  #BackRed      : 0
% 4.18/1.70  
% 4.18/1.70  #Partial instantiations: 0
% 4.18/1.70  #Strategies tried      : 1
% 4.18/1.70  
% 4.18/1.70  Timing (in seconds)
% 4.18/1.70  ----------------------
% 4.18/1.70  Preprocessing        : 0.31
% 4.18/1.70  Parsing              : 0.16
% 4.18/1.70  CNF conversion       : 0.03
% 4.18/1.70  Main loop            : 0.63
% 4.18/1.70  Inferencing          : 0.24
% 4.18/1.70  Reduction            : 0.16
% 4.18/1.70  Demodulation         : 0.11
% 4.18/1.70  BG Simplification    : 0.03
% 4.18/1.70  Subsumption          : 0.16
% 4.18/1.70  Abstraction          : 0.02
% 4.18/1.70  MUC search           : 0.00
% 4.18/1.70  Cooper               : 0.00
% 4.18/1.70  Total                : 0.97
% 4.18/1.70  Index Insertion      : 0.00
% 4.18/1.70  Index Deletion       : 0.00
% 4.18/1.71  Index Matching       : 0.00
% 4.18/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
