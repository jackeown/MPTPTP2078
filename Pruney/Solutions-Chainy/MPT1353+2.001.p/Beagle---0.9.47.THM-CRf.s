%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:51 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 6.75s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 166 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 390 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_6',u1_pre_topc('#skF_5'))
    | ~ v1_tops_2('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_47,plain,(
    ~ v1_tops_2('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_71,c_4])).

tff(c_54,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_36,c_54])).

tff(c_399,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_4'(A_96,B_97),B_97)
      | v1_tops_2(B_97,A_96)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96))))
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_404,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v1_tops_2('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_399])).

tff(c_408,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v1_tops_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_404])).

tff(c_409,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_408])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_413,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6'),B_98)
      | ~ r1_tarski('#skF_6',B_98) ) ),
    inference(resolution,[status(thm)],[c_409,c_2])).

tff(c_470,plain,(
    ! [B_106,B_107] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6'),B_106)
      | ~ r1_tarski(B_107,B_106)
      | ~ r1_tarski('#skF_6',B_107) ) ),
    inference(resolution,[status(thm)],[c_413,c_2])).

tff(c_490,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_470])).

tff(c_504,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_490])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( r1_tarski(C_10,A_6)
      | ~ r2_hidden(C_10,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_520,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_504,c_8])).

tff(c_46,plain,
    ( v1_tops_2('#skF_6','#skF_5')
    | r1_tarski('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    r1_tarski('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46])).

tff(c_488,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),u1_pre_topc('#skF_5'))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_470])).

tff(c_501,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_488])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_166,plain,(
    ! [B_68,A_69] :
      ( v3_pre_topc(B_68,A_69)
      | ~ r2_hidden(B_68,u1_pre_topc(A_69))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_171,plain,(
    ! [A_11,A_69] :
      ( v3_pre_topc(A_11,A_69)
      | ~ r2_hidden(A_11,u1_pre_topc(A_69))
      | ~ l1_pre_topc(A_69)
      | ~ r1_tarski(A_11,u1_struct_0(A_69)) ) ),
    inference(resolution,[status(thm)],[c_22,c_166])).

tff(c_507,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_501,c_171])).

tff(c_512,plain,
    ( v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_507])).

tff(c_602,plain,(
    v3_pre_topc('#skF_4'('#skF_5','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_512])).

tff(c_30,plain,(
    ! [A_16,B_22] :
      ( ~ v3_pre_topc('#skF_4'(A_16,B_22),A_16)
      | v1_tops_2(B_22,A_16)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16))))
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_604,plain,
    ( v1_tops_2('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_602,c_30])).

tff(c_607,plain,(
    v1_tops_2('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_604])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_607])).

tff(c_610,plain,(
    ~ r1_tarski('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_618,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(A_120,B_121)
      | ~ m1_subset_1(A_120,k1_zfmisc_1(B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_622,plain,(
    r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_36,c_618])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_648,plain,(
    ! [C_129,B_130,A_131] :
      ( r2_hidden(C_129,B_130)
      | ~ r2_hidden(C_129,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_673,plain,(
    ! [A_141,B_142,B_143] :
      ( r2_hidden('#skF_1'(A_141,B_142),B_143)
      | ~ r1_tarski(A_141,B_143)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_6,c_648])).

tff(c_686,plain,(
    ! [A_141,B_142,A_6] :
      ( r1_tarski('#skF_1'(A_141,B_142),A_6)
      | ~ r1_tarski(A_141,k1_zfmisc_1(A_6))
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_673,c_8])).

tff(c_611,plain,(
    v1_tops_2('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1185,plain,(
    ! [C_210,A_211,B_212] :
      ( v3_pre_topc(C_210,A_211)
      | ~ r2_hidden(C_210,B_212)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ v1_tops_2(B_212,A_211)
      | ~ m1_subset_1(B_212,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211))))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2090,plain,(
    ! [A_281,B_282,A_283] :
      ( v3_pre_topc('#skF_1'(A_281,B_282),A_283)
      | ~ m1_subset_1('#skF_1'(A_281,B_282),k1_zfmisc_1(u1_struct_0(A_283)))
      | ~ v1_tops_2(A_281,A_283)
      | ~ m1_subset_1(A_281,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_283))))
      | ~ l1_pre_topc(A_283)
      | r1_tarski(A_281,B_282) ) ),
    inference(resolution,[status(thm)],[c_6,c_1185])).

tff(c_3383,plain,(
    ! [A_389,B_390,A_391] :
      ( v3_pre_topc('#skF_1'(A_389,B_390),A_391)
      | ~ v1_tops_2(A_389,A_391)
      | ~ m1_subset_1(A_389,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_391))))
      | ~ l1_pre_topc(A_391)
      | r1_tarski(A_389,B_390)
      | ~ r1_tarski('#skF_1'(A_389,B_390),u1_struct_0(A_391)) ) ),
    inference(resolution,[status(thm)],[c_22,c_2090])).

tff(c_3388,plain,(
    ! [B_390] :
      ( v3_pre_topc('#skF_1'('#skF_6',B_390),'#skF_5')
      | ~ v1_tops_2('#skF_6','#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | r1_tarski('#skF_6',B_390)
      | ~ r1_tarski('#skF_1'('#skF_6',B_390),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_3383])).

tff(c_3393,plain,(
    ! [B_392] :
      ( v3_pre_topc('#skF_1'('#skF_6',B_392),'#skF_5')
      | r1_tarski('#skF_6',B_392)
      | ~ r1_tarski('#skF_1'('#skF_6',B_392),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_611,c_3388])).

tff(c_3401,plain,(
    ! [B_142] :
      ( v3_pre_topc('#skF_1'('#skF_6',B_142),'#skF_5')
      | ~ r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | r1_tarski('#skF_6',B_142) ) ),
    inference(resolution,[status(thm)],[c_686,c_3393])).

tff(c_3408,plain,(
    ! [B_393] :
      ( v3_pre_topc('#skF_1'('#skF_6',B_393),'#skF_5')
      | r1_tarski('#skF_6',B_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_3401])).

tff(c_739,plain,(
    ! [B_157,A_158] :
      ( r2_hidden(B_157,u1_pre_topc(A_158))
      | ~ v3_pre_topc(B_157,A_158)
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0(A_158)))
      | ~ l1_pre_topc(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_745,plain,(
    ! [A_159,A_160] :
      ( r2_hidden(A_159,u1_pre_topc(A_160))
      | ~ v3_pre_topc(A_159,A_160)
      | ~ l1_pre_topc(A_160)
      | ~ r1_tarski(A_159,u1_struct_0(A_160)) ) ),
    inference(resolution,[status(thm)],[c_22,c_739])).

tff(c_2655,plain,(
    ! [A_324,A_325] :
      ( r1_tarski(A_324,u1_pre_topc(A_325))
      | ~ v3_pre_topc('#skF_1'(A_324,u1_pre_topc(A_325)),A_325)
      | ~ l1_pre_topc(A_325)
      | ~ r1_tarski('#skF_1'(A_324,u1_pre_topc(A_325)),u1_struct_0(A_325)) ) ),
    inference(resolution,[status(thm)],[c_745,c_4])).

tff(c_2671,plain,(
    ! [A_141,A_325] :
      ( ~ v3_pre_topc('#skF_1'(A_141,u1_pre_topc(A_325)),A_325)
      | ~ l1_pre_topc(A_325)
      | ~ r1_tarski(A_141,k1_zfmisc_1(u1_struct_0(A_325)))
      | r1_tarski(A_141,u1_pre_topc(A_325)) ) ),
    inference(resolution,[status(thm)],[c_686,c_2655])).

tff(c_3412,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ r1_tarski('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | r1_tarski('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(resolution,[status(thm)],[c_3408,c_2671])).

tff(c_3419,plain,(
    r1_tarski('#skF_6',u1_pre_topc('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_38,c_3412])).

tff(c_3421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_3419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.34  
% 6.75/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.34  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 6.75/2.34  
% 6.75/2.34  %Foreground sorts:
% 6.75/2.34  
% 6.75/2.34  
% 6.75/2.34  %Background operators:
% 6.75/2.34  
% 6.75/2.34  
% 6.75/2.34  %Foreground operators:
% 6.75/2.34  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.75/2.34  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.75/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.75/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.75/2.34  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 6.75/2.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.75/2.34  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.75/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.75/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.75/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.75/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.75/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.75/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.75/2.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.75/2.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.75/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.75/2.34  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.75/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.75/2.34  
% 6.75/2.36  tff(f_76, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tops_2)).
% 6.75/2.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.75/2.36  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.75/2.36  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_2)).
% 6.75/2.36  tff(f_39, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.75/2.36  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 6.75/2.36  tff(c_40, plain, (~r1_tarski('#skF_6', u1_pre_topc('#skF_5')) | ~v1_tops_2('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.75/2.36  tff(c_47, plain, (~v1_tops_2('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 6.75/2.36  tff(c_38, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.75/2.36  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.75/2.36  tff(c_71, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.36  tff(c_80, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(resolution, [status(thm)], [c_71, c_4])).
% 6.75/2.36  tff(c_54, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.75/2.36  tff(c_58, plain, (r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36, c_54])).
% 6.75/2.36  tff(c_399, plain, (![A_96, B_97]: (r2_hidden('#skF_4'(A_96, B_97), B_97) | v1_tops_2(B_97, A_96) | ~m1_subset_1(B_97, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_96)))) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.36  tff(c_404, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v1_tops_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_399])).
% 6.75/2.36  tff(c_408, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v1_tops_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_404])).
% 6.75/2.36  tff(c_409, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_47, c_408])).
% 6.75/2.36  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.36  tff(c_413, plain, (![B_98]: (r2_hidden('#skF_4'('#skF_5', '#skF_6'), B_98) | ~r1_tarski('#skF_6', B_98))), inference(resolution, [status(thm)], [c_409, c_2])).
% 6.75/2.36  tff(c_470, plain, (![B_106, B_107]: (r2_hidden('#skF_4'('#skF_5', '#skF_6'), B_106) | ~r1_tarski(B_107, B_106) | ~r1_tarski('#skF_6', B_107))), inference(resolution, [status(thm)], [c_413, c_2])).
% 6.75/2.36  tff(c_490, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_470])).
% 6.75/2.36  tff(c_504, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_490])).
% 6.75/2.36  tff(c_8, plain, (![C_10, A_6]: (r1_tarski(C_10, A_6) | ~r2_hidden(C_10, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.75/2.36  tff(c_520, plain, (r1_tarski('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_504, c_8])).
% 6.75/2.36  tff(c_46, plain, (v1_tops_2('#skF_6', '#skF_5') | r1_tarski('#skF_6', u1_pre_topc('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.75/2.36  tff(c_64, plain, (r1_tarski('#skF_6', u1_pre_topc('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_47, c_46])).
% 6.75/2.36  tff(c_488, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), u1_pre_topc('#skF_5')) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_470])).
% 6.75/2.36  tff(c_501, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_488])).
% 6.75/2.36  tff(c_22, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.75/2.36  tff(c_166, plain, (![B_68, A_69]: (v3_pre_topc(B_68, A_69) | ~r2_hidden(B_68, u1_pre_topc(A_69)) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.75/2.36  tff(c_171, plain, (![A_11, A_69]: (v3_pre_topc(A_11, A_69) | ~r2_hidden(A_11, u1_pre_topc(A_69)) | ~l1_pre_topc(A_69) | ~r1_tarski(A_11, u1_struct_0(A_69)))), inference(resolution, [status(thm)], [c_22, c_166])).
% 6.75/2.36  tff(c_507, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | ~r1_tarski('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_501, c_171])).
% 6.75/2.36  tff(c_512, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5') | ~r1_tarski('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_507])).
% 6.75/2.36  tff(c_602, plain, (v3_pre_topc('#skF_4'('#skF_5', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_512])).
% 6.75/2.36  tff(c_30, plain, (![A_16, B_22]: (~v3_pre_topc('#skF_4'(A_16, B_22), A_16) | v1_tops_2(B_22, A_16) | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_16)))) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.36  tff(c_604, plain, (v1_tops_2('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_602, c_30])).
% 6.75/2.36  tff(c_607, plain, (v1_tops_2('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_604])).
% 6.75/2.36  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_607])).
% 6.75/2.36  tff(c_610, plain, (~r1_tarski('#skF_6', u1_pre_topc('#skF_5'))), inference(splitRight, [status(thm)], [c_40])).
% 6.75/2.36  tff(c_618, plain, (![A_120, B_121]: (r1_tarski(A_120, B_121) | ~m1_subset_1(A_120, k1_zfmisc_1(B_121)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.75/2.36  tff(c_622, plain, (r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36, c_618])).
% 6.75/2.36  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.36  tff(c_648, plain, (![C_129, B_130, A_131]: (r2_hidden(C_129, B_130) | ~r2_hidden(C_129, A_131) | ~r1_tarski(A_131, B_130))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.75/2.36  tff(c_673, plain, (![A_141, B_142, B_143]: (r2_hidden('#skF_1'(A_141, B_142), B_143) | ~r1_tarski(A_141, B_143) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_6, c_648])).
% 6.75/2.36  tff(c_686, plain, (![A_141, B_142, A_6]: (r1_tarski('#skF_1'(A_141, B_142), A_6) | ~r1_tarski(A_141, k1_zfmisc_1(A_6)) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_673, c_8])).
% 6.75/2.36  tff(c_611, plain, (v1_tops_2('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 6.75/2.36  tff(c_1185, plain, (![C_210, A_211, B_212]: (v3_pre_topc(C_210, A_211) | ~r2_hidden(C_210, B_212) | ~m1_subset_1(C_210, k1_zfmisc_1(u1_struct_0(A_211))) | ~v1_tops_2(B_212, A_211) | ~m1_subset_1(B_212, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_211)))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.75/2.36  tff(c_2090, plain, (![A_281, B_282, A_283]: (v3_pre_topc('#skF_1'(A_281, B_282), A_283) | ~m1_subset_1('#skF_1'(A_281, B_282), k1_zfmisc_1(u1_struct_0(A_283))) | ~v1_tops_2(A_281, A_283) | ~m1_subset_1(A_281, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_283)))) | ~l1_pre_topc(A_283) | r1_tarski(A_281, B_282))), inference(resolution, [status(thm)], [c_6, c_1185])).
% 6.75/2.36  tff(c_3383, plain, (![A_389, B_390, A_391]: (v3_pre_topc('#skF_1'(A_389, B_390), A_391) | ~v1_tops_2(A_389, A_391) | ~m1_subset_1(A_389, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_391)))) | ~l1_pre_topc(A_391) | r1_tarski(A_389, B_390) | ~r1_tarski('#skF_1'(A_389, B_390), u1_struct_0(A_391)))), inference(resolution, [status(thm)], [c_22, c_2090])).
% 6.75/2.36  tff(c_3388, plain, (![B_390]: (v3_pre_topc('#skF_1'('#skF_6', B_390), '#skF_5') | ~v1_tops_2('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | r1_tarski('#skF_6', B_390) | ~r1_tarski('#skF_1'('#skF_6', B_390), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36, c_3383])).
% 6.75/2.36  tff(c_3393, plain, (![B_392]: (v3_pre_topc('#skF_1'('#skF_6', B_392), '#skF_5') | r1_tarski('#skF_6', B_392) | ~r1_tarski('#skF_1'('#skF_6', B_392), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_611, c_3388])).
% 6.75/2.36  tff(c_3401, plain, (![B_142]: (v3_pre_topc('#skF_1'('#skF_6', B_142), '#skF_5') | ~r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | r1_tarski('#skF_6', B_142))), inference(resolution, [status(thm)], [c_686, c_3393])).
% 6.75/2.36  tff(c_3408, plain, (![B_393]: (v3_pre_topc('#skF_1'('#skF_6', B_393), '#skF_5') | r1_tarski('#skF_6', B_393))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_3401])).
% 6.75/2.36  tff(c_739, plain, (![B_157, A_158]: (r2_hidden(B_157, u1_pre_topc(A_158)) | ~v3_pre_topc(B_157, A_158) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0(A_158))) | ~l1_pre_topc(A_158))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.75/2.36  tff(c_745, plain, (![A_159, A_160]: (r2_hidden(A_159, u1_pre_topc(A_160)) | ~v3_pre_topc(A_159, A_160) | ~l1_pre_topc(A_160) | ~r1_tarski(A_159, u1_struct_0(A_160)))), inference(resolution, [status(thm)], [c_22, c_739])).
% 6.75/2.36  tff(c_2655, plain, (![A_324, A_325]: (r1_tarski(A_324, u1_pre_topc(A_325)) | ~v3_pre_topc('#skF_1'(A_324, u1_pre_topc(A_325)), A_325) | ~l1_pre_topc(A_325) | ~r1_tarski('#skF_1'(A_324, u1_pre_topc(A_325)), u1_struct_0(A_325)))), inference(resolution, [status(thm)], [c_745, c_4])).
% 6.75/2.36  tff(c_2671, plain, (![A_141, A_325]: (~v3_pre_topc('#skF_1'(A_141, u1_pre_topc(A_325)), A_325) | ~l1_pre_topc(A_325) | ~r1_tarski(A_141, k1_zfmisc_1(u1_struct_0(A_325))) | r1_tarski(A_141, u1_pre_topc(A_325)))), inference(resolution, [status(thm)], [c_686, c_2655])).
% 6.75/2.36  tff(c_3412, plain, (~l1_pre_topc('#skF_5') | ~r1_tarski('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | r1_tarski('#skF_6', u1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_3408, c_2671])).
% 6.75/2.36  tff(c_3419, plain, (r1_tarski('#skF_6', u1_pre_topc('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_38, c_3412])).
% 6.75/2.36  tff(c_3421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_3419])).
% 6.75/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.75/2.36  
% 6.75/2.36  Inference rules
% 6.75/2.36  ----------------------
% 6.75/2.36  #Ref     : 0
% 6.75/2.36  #Sup     : 840
% 6.75/2.36  #Fact    : 0
% 6.75/2.36  #Define  : 0
% 6.75/2.36  #Split   : 16
% 6.75/2.36  #Chain   : 0
% 6.75/2.36  #Close   : 0
% 6.75/2.36  
% 6.75/2.36  Ordering : KBO
% 6.75/2.36  
% 6.75/2.36  Simplification rules
% 6.75/2.36  ----------------------
% 6.75/2.36  #Subsume      : 145
% 6.75/2.36  #Demod        : 58
% 6.75/2.36  #Tautology    : 39
% 6.75/2.36  #SimpNegUnit  : 5
% 6.75/2.36  #BackRed      : 0
% 6.75/2.36  
% 6.75/2.36  #Partial instantiations: 0
% 6.75/2.36  #Strategies tried      : 1
% 6.75/2.36  
% 6.75/2.36  Timing (in seconds)
% 6.75/2.36  ----------------------
% 6.75/2.36  Preprocessing        : 0.29
% 6.75/2.36  Parsing              : 0.16
% 6.75/2.36  CNF conversion       : 0.02
% 6.75/2.36  Main loop            : 1.31
% 6.75/2.36  Inferencing          : 0.39
% 6.75/2.36  Reduction            : 0.30
% 6.75/2.36  Demodulation         : 0.19
% 6.75/2.36  BG Simplification    : 0.04
% 6.75/2.36  Subsumption          : 0.46
% 6.75/2.36  Abstraction          : 0.05
% 6.75/2.36  MUC search           : 0.00
% 6.75/2.36  Cooper               : 0.00
% 6.75/2.36  Total                : 1.63
% 6.75/2.36  Index Insertion      : 0.00
% 6.75/2.36  Index Deletion       : 0.00
% 6.75/2.36  Index Matching       : 0.00
% 6.75/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
