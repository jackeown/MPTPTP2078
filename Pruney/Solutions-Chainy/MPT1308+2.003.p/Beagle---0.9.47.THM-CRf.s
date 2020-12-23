%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 137 expanded)
%              Number of leaves         :   29 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :  137 ( 376 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_63,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_72,axiom,(
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

tff(c_511,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(A_155),B_156),u1_pre_topc(A_155))
      | ~ r1_tarski(B_156,u1_pre_topc(A_155))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155))))
      | ~ v2_pre_topc(A_155)
      | ~ l1_pre_topc(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_50,plain,(
    ! [A_26] :
      ( m1_subset_1(u1_pre_topc(A_26),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26))))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_86,plain,(
    ! [A_48,C_49,B_50] :
      ( m1_subset_1(A_48,C_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(C_49))
      | ~ r2_hidden(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_91,plain,(
    ! [A_48,A_26] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ r2_hidden(A_48,u1_pre_topc(A_26))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_50,c_86])).

tff(c_173,plain,(
    ! [B_72,A_73] :
      ( v3_pre_topc(B_72,A_73)
      | ~ r2_hidden(B_72,u1_pre_topc(A_73))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_180,plain,(
    ! [A_48,A_26] :
      ( v3_pre_topc(A_48,A_26)
      | ~ r2_hidden(A_48,u1_pre_topc(A_26))
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_91,c_173])).

tff(c_538,plain,(
    ! [A_157,B_158] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(A_157),B_158),A_157)
      | ~ r1_tarski(B_158,u1_pre_topc(A_157))
      | ~ m1_subset_1(B_158,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_157))))
      | ~ v2_pre_topc(A_157)
      | ~ l1_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_511,c_180])).

tff(c_542,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_538])).

tff(c_548,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'),'#skF_7'),'#skF_6')
    | ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_542])).

tff(c_549,plain,(
    ~ r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_548])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [A_40,B_41] :
      ( ~ r2_hidden('#skF_1'(A_40,B_41),B_41)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_78,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_1,B_2,B_45] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_45)
      | ~ r1_tarski(A_1,B_45)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_62,plain,(
    v1_tops_2('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_92,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_48,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_578,plain,(
    ! [C_171,A_172,B_173] :
      ( v3_pre_topc(C_171,A_172)
      | ~ r2_hidden(C_171,B_173)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ v1_tops_2(B_173,A_172)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_172))))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1217,plain,(
    ! [A_271,B_272,A_273] :
      ( v3_pre_topc('#skF_1'(A_271,B_272),A_273)
      | ~ m1_subset_1('#skF_1'(A_271,B_272),k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ v1_tops_2(A_271,A_273)
      | ~ m1_subset_1(A_271,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_273))))
      | ~ l1_pre_topc(A_273)
      | r1_tarski(A_271,B_272) ) ),
    inference(resolution,[status(thm)],[c_6,c_578])).

tff(c_1233,plain,(
    ! [A_271,B_272] :
      ( v3_pre_topc('#skF_1'(A_271,B_272),'#skF_6')
      | ~ v1_tops_2(A_271,'#skF_6')
      | ~ m1_subset_1(A_271,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
      | ~ l1_pre_topc('#skF_6')
      | r1_tarski(A_271,B_272)
      | ~ r2_hidden('#skF_1'(A_271,B_272),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_92,c_1217])).

tff(c_1240,plain,(
    ! [A_274,B_275] :
      ( v3_pre_topc('#skF_1'(A_274,B_275),'#skF_6')
      | ~ v1_tops_2(A_274,'#skF_6')
      | ~ m1_subset_1(A_274,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))
      | r1_tarski(A_274,B_275)
      | ~ r2_hidden('#skF_1'(A_274,B_275),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1233])).

tff(c_1257,plain,(
    ! [B_275] :
      ( v3_pre_topc('#skF_1'('#skF_7',B_275),'#skF_6')
      | ~ v1_tops_2('#skF_7','#skF_6')
      | r1_tarski('#skF_7',B_275)
      | ~ r2_hidden('#skF_1'('#skF_7',B_275),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_64,c_1240])).

tff(c_1276,plain,(
    ! [B_276] :
      ( v3_pre_topc('#skF_1'('#skF_7',B_276),'#skF_6')
      | r1_tarski('#skF_7',B_276)
      | ~ r2_hidden('#skF_1'('#skF_7',B_276),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1257])).

tff(c_116,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,u1_pre_topc(A_58))
      | ~ v3_pre_topc(B_57,A_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_119,plain,(
    ! [A_48] :
      ( r2_hidden(A_48,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc(A_48,'#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r2_hidden(A_48,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_92,c_116])).

tff(c_123,plain,(
    ! [A_59] :
      ( r2_hidden(A_59,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc(A_59,'#skF_6')
      | ~ r2_hidden(A_59,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_119])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_pre_topc('#skF_6'))
      | ~ v3_pre_topc('#skF_1'(A_1,u1_pre_topc('#skF_6')),'#skF_6')
      | ~ r2_hidden('#skF_1'(A_1,u1_pre_topc('#skF_6')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_123,c_4])).

tff(c_1280,plain,
    ( r1_tarski('#skF_7',u1_pre_topc('#skF_6'))
    | ~ r2_hidden('#skF_1'('#skF_7',u1_pre_topc('#skF_6')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_1276,c_134])).

tff(c_1283,plain,(
    ~ r2_hidden('#skF_1'('#skF_7',u1_pre_topc('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_549,c_1280])).

tff(c_1286,plain,
    ( ~ r1_tarski('#skF_7','#skF_7')
    | r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(resolution,[status(thm)],[c_84,c_1283])).

tff(c_1292,plain,(
    r1_tarski('#skF_7',u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1286])).

tff(c_1294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_549,c_1292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n007.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 17:58:36 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.80  
% 4.11/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.80  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k5_setfam_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_3 > #skF_1 > #skF_5
% 4.11/1.80  
% 4.11/1.80  %Foreground sorts:
% 4.11/1.80  
% 4.11/1.80  
% 4.11/1.80  %Background operators:
% 4.11/1.80  
% 4.11/1.80  
% 4.11/1.80  %Foreground operators:
% 4.11/1.80  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.11/1.80  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.11/1.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.11/1.80  tff('#skF_4', type, '#skF_4': $i > $i).
% 4.11/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.80  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 4.11/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.11/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.11/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.11/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.80  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.11/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.80  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.11/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.11/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.11/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.80  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.11/1.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.11/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.80  
% 4.11/1.83  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) => v3_pre_topc(k5_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tops_2)).
% 4.11/1.83  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 4.11/1.83  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.11/1.83  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 4.11/1.83  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 4.11/1.83  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.11/1.83  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 4.11/1.83  tff(c_60, plain, (~v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.83  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.83  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.83  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.83  tff(c_511, plain, (![A_155, B_156]: (r2_hidden(k5_setfam_1(u1_struct_0(A_155), B_156), u1_pre_topc(A_155)) | ~r1_tarski(B_156, u1_pre_topc(A_155)) | ~m1_subset_1(B_156, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_155)))) | ~v2_pre_topc(A_155) | ~l1_pre_topc(A_155))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.11/1.83  tff(c_50, plain, (![A_26]: (m1_subset_1(u1_pre_topc(A_26), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_26)))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.11/1.83  tff(c_86, plain, (![A_48, C_49, B_50]: (m1_subset_1(A_48, C_49) | ~m1_subset_1(B_50, k1_zfmisc_1(C_49)) | ~r2_hidden(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.11/1.83  tff(c_91, plain, (![A_48, A_26]: (m1_subset_1(A_48, k1_zfmisc_1(u1_struct_0(A_26))) | ~r2_hidden(A_48, u1_pre_topc(A_26)) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_50, c_86])).
% 4.11/1.83  tff(c_173, plain, (![B_72, A_73]: (v3_pre_topc(B_72, A_73) | ~r2_hidden(B_72, u1_pre_topc(A_73)) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.11/1.83  tff(c_180, plain, (![A_48, A_26]: (v3_pre_topc(A_48, A_26) | ~r2_hidden(A_48, u1_pre_topc(A_26)) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_91, c_173])).
% 4.11/1.83  tff(c_538, plain, (![A_157, B_158]: (v3_pre_topc(k5_setfam_1(u1_struct_0(A_157), B_158), A_157) | ~r1_tarski(B_158, u1_pre_topc(A_157)) | ~m1_subset_1(B_158, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_157)))) | ~v2_pre_topc(A_157) | ~l1_pre_topc(A_157))), inference(resolution, [status(thm)], [c_511, c_180])).
% 4.11/1.83  tff(c_542, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_64, c_538])).
% 4.11/1.83  tff(c_548, plain, (v3_pre_topc(k5_setfam_1(u1_struct_0('#skF_6'), '#skF_7'), '#skF_6') | ~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_542])).
% 4.11/1.83  tff(c_549, plain, (~r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_548])).
% 4.11/1.83  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.83  tff(c_70, plain, (![A_40, B_41]: (~r2_hidden('#skF_1'(A_40, B_41), B_41) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.83  tff(c_75, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_70])).
% 4.11/1.83  tff(c_78, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.83  tff(c_84, plain, (![A_1, B_2, B_45]: (r2_hidden('#skF_1'(A_1, B_2), B_45) | ~r1_tarski(A_1, B_45) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_78])).
% 4.11/1.83  tff(c_62, plain, (v1_tops_2('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.83  tff(c_92, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~r2_hidden(A_48, '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_86])).
% 4.11/1.83  tff(c_578, plain, (![C_171, A_172, B_173]: (v3_pre_topc(C_171, A_172) | ~r2_hidden(C_171, B_173) | ~m1_subset_1(C_171, k1_zfmisc_1(u1_struct_0(A_172))) | ~v1_tops_2(B_173, A_172) | ~m1_subset_1(B_173, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_172)))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.11/1.83  tff(c_1217, plain, (![A_271, B_272, A_273]: (v3_pre_topc('#skF_1'(A_271, B_272), A_273) | ~m1_subset_1('#skF_1'(A_271, B_272), k1_zfmisc_1(u1_struct_0(A_273))) | ~v1_tops_2(A_271, A_273) | ~m1_subset_1(A_271, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_273)))) | ~l1_pre_topc(A_273) | r1_tarski(A_271, B_272))), inference(resolution, [status(thm)], [c_6, c_578])).
% 4.11/1.83  tff(c_1233, plain, (![A_271, B_272]: (v3_pre_topc('#skF_1'(A_271, B_272), '#skF_6') | ~v1_tops_2(A_271, '#skF_6') | ~m1_subset_1(A_271, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) | ~l1_pre_topc('#skF_6') | r1_tarski(A_271, B_272) | ~r2_hidden('#skF_1'(A_271, B_272), '#skF_7'))), inference(resolution, [status(thm)], [c_92, c_1217])).
% 4.11/1.83  tff(c_1240, plain, (![A_274, B_275]: (v3_pre_topc('#skF_1'(A_274, B_275), '#skF_6') | ~v1_tops_2(A_274, '#skF_6') | ~m1_subset_1(A_274, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_6')))) | r1_tarski(A_274, B_275) | ~r2_hidden('#skF_1'(A_274, B_275), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1233])).
% 4.11/1.83  tff(c_1257, plain, (![B_275]: (v3_pre_topc('#skF_1'('#skF_7', B_275), '#skF_6') | ~v1_tops_2('#skF_7', '#skF_6') | r1_tarski('#skF_7', B_275) | ~r2_hidden('#skF_1'('#skF_7', B_275), '#skF_7'))), inference(resolution, [status(thm)], [c_64, c_1240])).
% 4.11/1.83  tff(c_1276, plain, (![B_276]: (v3_pre_topc('#skF_1'('#skF_7', B_276), '#skF_6') | r1_tarski('#skF_7', B_276) | ~r2_hidden('#skF_1'('#skF_7', B_276), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1257])).
% 4.11/1.83  tff(c_116, plain, (![B_57, A_58]: (r2_hidden(B_57, u1_pre_topc(A_58)) | ~v3_pre_topc(B_57, A_58) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.11/1.83  tff(c_119, plain, (![A_48]: (r2_hidden(A_48, u1_pre_topc('#skF_6')) | ~v3_pre_topc(A_48, '#skF_6') | ~l1_pre_topc('#skF_6') | ~r2_hidden(A_48, '#skF_7'))), inference(resolution, [status(thm)], [c_92, c_116])).
% 4.11/1.83  tff(c_123, plain, (![A_59]: (r2_hidden(A_59, u1_pre_topc('#skF_6')) | ~v3_pre_topc(A_59, '#skF_6') | ~r2_hidden(A_59, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_119])).
% 4.11/1.83  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.11/1.83  tff(c_134, plain, (![A_1]: (r1_tarski(A_1, u1_pre_topc('#skF_6')) | ~v3_pre_topc('#skF_1'(A_1, u1_pre_topc('#skF_6')), '#skF_6') | ~r2_hidden('#skF_1'(A_1, u1_pre_topc('#skF_6')), '#skF_7'))), inference(resolution, [status(thm)], [c_123, c_4])).
% 4.11/1.83  tff(c_1280, plain, (r1_tarski('#skF_7', u1_pre_topc('#skF_6')) | ~r2_hidden('#skF_1'('#skF_7', u1_pre_topc('#skF_6')), '#skF_7')), inference(resolution, [status(thm)], [c_1276, c_134])).
% 4.11/1.83  tff(c_1283, plain, (~r2_hidden('#skF_1'('#skF_7', u1_pre_topc('#skF_6')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_549, c_549, c_1280])).
% 4.11/1.83  tff(c_1286, plain, (~r1_tarski('#skF_7', '#skF_7') | r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_84, c_1283])).
% 4.11/1.83  tff(c_1292, plain, (r1_tarski('#skF_7', u1_pre_topc('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1286])).
% 4.11/1.83  tff(c_1294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_549, c_1292])).
% 4.11/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.83  
% 4.11/1.83  Inference rules
% 4.11/1.83  ----------------------
% 4.11/1.83  #Ref     : 0
% 4.11/1.83  #Sup     : 254
% 4.11/1.83  #Fact    : 4
% 4.11/1.83  #Define  : 0
% 4.11/1.83  #Split   : 4
% 4.11/1.83  #Chain   : 0
% 4.11/1.83  #Close   : 0
% 4.11/1.83  
% 4.11/1.83  Ordering : KBO
% 4.11/1.83  
% 4.11/1.83  Simplification rules
% 4.11/1.83  ----------------------
% 4.11/1.83  #Subsume      : 39
% 4.11/1.83  #Demod        : 92
% 4.11/1.83  #Tautology    : 54
% 4.11/1.83  #SimpNegUnit  : 4
% 4.11/1.83  #BackRed      : 0
% 4.11/1.83  
% 4.11/1.83  #Partial instantiations: 0
% 4.11/1.83  #Strategies tried      : 1
% 4.11/1.83  
% 4.11/1.83  Timing (in seconds)
% 4.11/1.83  ----------------------
% 4.32/1.84  Preprocessing        : 0.35
% 4.32/1.84  Parsing              : 0.19
% 4.32/1.84  CNF conversion       : 0.02
% 4.32/1.84  Main loop            : 0.62
% 4.32/1.84  Inferencing          : 0.24
% 4.32/1.84  Reduction            : 0.15
% 4.32/1.84  Demodulation         : 0.10
% 4.32/1.84  BG Simplification    : 0.03
% 4.32/1.84  Subsumption          : 0.16
% 4.32/1.84  Abstraction          : 0.02
% 4.32/1.84  MUC search           : 0.00
% 4.32/1.84  Cooper               : 0.00
% 4.32/1.84  Total                : 1.03
% 4.32/1.84  Index Insertion      : 0.00
% 4.32/1.84  Index Deletion       : 0.00
% 4.32/1.84  Index Matching       : 0.00
% 4.32/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
