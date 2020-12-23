%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:52 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   63 (  94 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 ( 263 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( v1_tops_2(B,A)
            <=> r1_tarski(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( ( r1_tarski(B,C)
                  & v1_tops_2(C,A) )
               => v1_tops_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tops_2)).

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

tff(c_26,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12,plain,(
    ! [A_11] :
      ( m1_subset_1(u1_pre_topc(A_11),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_41,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_2'(A_37,B_38),B_38)
      | v1_tops_2(B_38,A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37))))
      | ~ l1_pre_topc(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_46,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_2'(A_11,u1_pre_topc(A_11)),u1_pre_topc(A_11))
      | v1_tops_2(u1_pre_topc(A_11),A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_86,plain,(
    ! [A_52,B_53] :
      ( m1_subset_1('#skF_2'(A_52,B_53),k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_tops_2(B_53,A_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_52))))
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [B_10,A_8] :
      ( v3_pre_topc(B_10,A_8)
      | ~ r2_hidden(B_10,u1_pre_topc(A_8))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_123,plain,(
    ! [A_60,B_61] :
      ( v3_pre_topc('#skF_2'(A_60,B_61),A_60)
      | ~ r2_hidden('#skF_2'(A_60,B_61),u1_pre_topc(A_60))
      | v1_tops_2(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60))))
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_86,c_8])).

tff(c_127,plain,(
    ! [A_62] :
      ( v3_pre_topc('#skF_2'(A_62,u1_pre_topc(A_62)),A_62)
      | ~ m1_subset_1(u1_pre_topc(A_62),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62))))
      | v1_tops_2(u1_pre_topc(A_62),A_62)
      | ~ l1_pre_topc(A_62) ) ),
    inference(resolution,[status(thm)],[c_46,c_123])).

tff(c_147,plain,(
    ! [A_66] :
      ( v3_pre_topc('#skF_2'(A_66,u1_pre_topc(A_66)),A_66)
      | v1_tops_2(u1_pre_topc(A_66),A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_12,c_127])).

tff(c_16,plain,(
    ! [A_12,B_18] :
      ( ~ v3_pre_topc('#skF_2'(A_12,B_18),A_12)
      | v1_tops_2(B_18,A_12)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_151,plain,(
    ! [A_67] :
      ( ~ m1_subset_1(u1_pre_topc(A_67),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67))))
      | v1_tops_2(u1_pre_topc(A_67),A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(resolution,[status(thm)],[c_147,c_16])).

tff(c_155,plain,(
    ! [A_11] :
      ( v1_tops_2(u1_pre_topc(A_11),A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_151])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_35,plain,(
    ~ v1_tops_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_34])).

tff(c_131,plain,(
    ! [B_63,A_64,C_65] :
      ( v1_tops_2(B_63,A_64)
      | ~ v1_tops_2(C_65,A_64)
      | ~ r1_tarski(B_63,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64))))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64))))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_157,plain,(
    ! [A_69] :
      ( v1_tops_2('#skF_4',A_69)
      | ~ v1_tops_2(u1_pre_topc('#skF_3'),A_69)
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ l1_pre_topc(A_69) ) ),
    inference(resolution,[status(thm)],[c_36,c_131])).

tff(c_161,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_157])).

tff(c_164,plain,
    ( v1_tops_2('#skF_4','#skF_3')
    | ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_161])).

tff(c_165,plain,(
    ~ v1_tops_2(u1_pre_topc('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_164])).

tff(c_168,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_155,c_165])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_168])).

tff(c_173,plain,(
    ~ r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_174,plain,(
    v1_tops_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

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

tff(c_251,plain,(
    ! [C_97,A_98,B_99] :
      ( v3_pre_topc(C_97,A_98)
      | ~ r2_hidden(C_97,B_99)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ v1_tops_2(B_99,A_98)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_98))))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_313,plain,(
    ! [A_122,B_123,C_124,A_125] :
      ( v3_pre_topc('#skF_1'(A_122,B_123,C_124),A_125)
      | ~ m1_subset_1('#skF_1'(A_122,B_123,C_124),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ v1_tops_2(B_123,A_125)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125)
      | r1_tarski(B_123,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_4,c_251])).

tff(c_319,plain,(
    ! [A_126,B_127,C_128] :
      ( v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_126)),B_127,C_128),A_126)
      | ~ v1_tops_2(B_127,A_126)
      | ~ l1_pre_topc(A_126)
      | r1_tarski(B_127,C_128)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126))))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))) ) ),
    inference(resolution,[status(thm)],[c_6,c_313])).

tff(c_191,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1('#skF_1'(A_80,B_81,C_82),A_80)
      | r1_tarski(B_81,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( r2_hidden(B_10,u1_pre_topc(A_8))
      | ~ v3_pre_topc(B_10,A_8)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_287,plain,(
    ! [A_112,B_113,C_114] :
      ( r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_112)),B_113,C_114),u1_pre_topc(A_112))
      | ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_112)),B_113,C_114),A_112)
      | ~ l1_pre_topc(A_112)
      | r1_tarski(B_113,C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112))))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) ) ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_295,plain,(
    ! [A_112,B_113] :
      ( ~ v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_112)),B_113,u1_pre_topc(A_112)),A_112)
      | ~ l1_pre_topc(A_112)
      | r1_tarski(B_113,u1_pre_topc(A_112))
      | ~ m1_subset_1(u1_pre_topc(A_112),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112))))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_325,plain,(
    ! [B_129,A_130] :
      ( ~ v1_tops_2(B_129,A_130)
      | ~ l1_pre_topc(A_130)
      | r1_tarski(B_129,u1_pre_topc(A_130))
      | ~ m1_subset_1(u1_pre_topc(A_130),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130))))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130)))) ) ),
    inference(resolution,[status(thm)],[c_319,c_295])).

tff(c_333,plain,(
    ! [B_134,A_135] :
      ( ~ v1_tops_2(B_134,A_135)
      | r1_tarski(B_134,u1_pre_topc(A_135))
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135))))
      | ~ l1_pre_topc(A_135) ) ),
    inference(resolution,[status(thm)],[c_12,c_325])).

tff(c_343,plain,
    ( ~ v1_tops_2('#skF_4','#skF_3')
    | r1_tarski('#skF_4',u1_pre_topc('#skF_3'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_348,plain,(
    r1_tarski('#skF_4',u1_pre_topc('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_174,c_343])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:23:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.33  
% 2.50/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.33  %$ v3_pre_topc > v1_tops_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.50/1.33  
% 2.50/1.33  %Foreground sorts:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Background operators:
% 2.50/1.33  
% 2.50/1.33  
% 2.50/1.33  %Foreground operators:
% 2.50/1.33  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.50/1.33  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.50/1.33  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.33  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.50/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.50/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.50/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.50/1.33  
% 2.50/1.35  tff(f_90, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> r1_tarski(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tops_2)).
% 2.50/1.35  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 2.50/1.35  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_tops_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_2)).
% 2.50/1.35  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.50/1.35  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((r1_tarski(B, C) & v1_tops_2(C, A)) => v1_tops_2(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_tops_2)).
% 2.50/1.35  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 2.50/1.35  tff(c_26, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.50/1.35  tff(c_12, plain, (![A_11]: (m1_subset_1(u1_pre_topc(A_11), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.50/1.35  tff(c_41, plain, (![A_37, B_38]: (r2_hidden('#skF_2'(A_37, B_38), B_38) | v1_tops_2(B_38, A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_37)))) | ~l1_pre_topc(A_37))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.35  tff(c_46, plain, (![A_11]: (r2_hidden('#skF_2'(A_11, u1_pre_topc(A_11)), u1_pre_topc(A_11)) | v1_tops_2(u1_pre_topc(A_11), A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_41])).
% 2.50/1.35  tff(c_86, plain, (![A_52, B_53]: (m1_subset_1('#skF_2'(A_52, B_53), k1_zfmisc_1(u1_struct_0(A_52))) | v1_tops_2(B_53, A_52) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_52)))) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.35  tff(c_8, plain, (![B_10, A_8]: (v3_pre_topc(B_10, A_8) | ~r2_hidden(B_10, u1_pre_topc(A_8)) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.50/1.35  tff(c_123, plain, (![A_60, B_61]: (v3_pre_topc('#skF_2'(A_60, B_61), A_60) | ~r2_hidden('#skF_2'(A_60, B_61), u1_pre_topc(A_60)) | v1_tops_2(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_60)))) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_86, c_8])).
% 2.50/1.35  tff(c_127, plain, (![A_62]: (v3_pre_topc('#skF_2'(A_62, u1_pre_topc(A_62)), A_62) | ~m1_subset_1(u1_pre_topc(A_62), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_62)))) | v1_tops_2(u1_pre_topc(A_62), A_62) | ~l1_pre_topc(A_62))), inference(resolution, [status(thm)], [c_46, c_123])).
% 2.50/1.35  tff(c_147, plain, (![A_66]: (v3_pre_topc('#skF_2'(A_66, u1_pre_topc(A_66)), A_66) | v1_tops_2(u1_pre_topc(A_66), A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_12, c_127])).
% 2.50/1.35  tff(c_16, plain, (![A_12, B_18]: (~v3_pre_topc('#skF_2'(A_12, B_18), A_12) | v1_tops_2(B_18, A_12) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.35  tff(c_151, plain, (![A_67]: (~m1_subset_1(u1_pre_topc(A_67), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_67)))) | v1_tops_2(u1_pre_topc(A_67), A_67) | ~l1_pre_topc(A_67))), inference(resolution, [status(thm)], [c_147, c_16])).
% 2.50/1.35  tff(c_155, plain, (![A_11]: (v1_tops_2(u1_pre_topc(A_11), A_11) | ~l1_pre_topc(A_11))), inference(resolution, [status(thm)], [c_12, c_151])).
% 2.50/1.35  tff(c_28, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_3')) | ~v1_tops_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.50/1.35  tff(c_35, plain, (~v1_tops_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.50/1.35  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.50/1.35  tff(c_34, plain, (v1_tops_2('#skF_4', '#skF_3') | r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.50/1.35  tff(c_36, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_35, c_34])).
% 2.50/1.35  tff(c_131, plain, (![B_63, A_64, C_65]: (v1_tops_2(B_63, A_64) | ~v1_tops_2(C_65, A_64) | ~r1_tarski(B_63, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64)))) | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64)))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.50/1.35  tff(c_157, plain, (![A_69]: (v1_tops_2('#skF_4', A_69) | ~v1_tops_2(u1_pre_topc('#skF_3'), A_69) | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69)))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69)))) | ~l1_pre_topc(A_69))), inference(resolution, [status(thm)], [c_36, c_131])).
% 2.50/1.35  tff(c_161, plain, (v1_tops_2('#skF_4', '#skF_3') | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_12, c_157])).
% 2.50/1.35  tff(c_164, plain, (v1_tops_2('#skF_4', '#skF_3') | ~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_161])).
% 2.50/1.35  tff(c_165, plain, (~v1_tops_2(u1_pre_topc('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_35, c_164])).
% 2.50/1.35  tff(c_168, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_155, c_165])).
% 2.50/1.35  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_168])).
% 2.50/1.35  tff(c_173, plain, (~r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 2.50/1.35  tff(c_174, plain, (v1_tops_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.50/1.35  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.35  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.35  tff(c_251, plain, (![C_97, A_98, B_99]: (v3_pre_topc(C_97, A_98) | ~r2_hidden(C_97, B_99) | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~v1_tops_2(B_99, A_98) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_98)))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.35  tff(c_313, plain, (![A_122, B_123, C_124, A_125]: (v3_pre_topc('#skF_1'(A_122, B_123, C_124), A_125) | ~m1_subset_1('#skF_1'(A_122, B_123, C_124), k1_zfmisc_1(u1_struct_0(A_125))) | ~v1_tops_2(B_123, A_125) | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125)))) | ~l1_pre_topc(A_125) | r1_tarski(B_123, C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(A_122)) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(resolution, [status(thm)], [c_4, c_251])).
% 2.50/1.35  tff(c_319, plain, (![A_126, B_127, C_128]: (v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_126)), B_127, C_128), A_126) | ~v1_tops_2(B_127, A_126) | ~l1_pre_topc(A_126) | r1_tarski(B_127, C_128) | ~m1_subset_1(C_128, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))) | ~m1_subset_1(B_127, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_126)))))), inference(resolution, [status(thm)], [c_6, c_313])).
% 2.50/1.35  tff(c_191, plain, (![A_80, B_81, C_82]: (m1_subset_1('#skF_1'(A_80, B_81, C_82), A_80) | r1_tarski(B_81, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(A_80)) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.35  tff(c_10, plain, (![B_10, A_8]: (r2_hidden(B_10, u1_pre_topc(A_8)) | ~v3_pre_topc(B_10, A_8) | ~m1_subset_1(B_10, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.50/1.35  tff(c_287, plain, (![A_112, B_113, C_114]: (r2_hidden('#skF_1'(k1_zfmisc_1(u1_struct_0(A_112)), B_113, C_114), u1_pre_topc(A_112)) | ~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_112)), B_113, C_114), A_112) | ~l1_pre_topc(A_112) | r1_tarski(B_113, C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))))), inference(resolution, [status(thm)], [c_191, c_10])).
% 2.50/1.35  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.50/1.35  tff(c_295, plain, (![A_112, B_113]: (~v3_pre_topc('#skF_1'(k1_zfmisc_1(u1_struct_0(A_112)), B_113, u1_pre_topc(A_112)), A_112) | ~l1_pre_topc(A_112) | r1_tarski(B_113, u1_pre_topc(A_112)) | ~m1_subset_1(u1_pre_topc(A_112), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_112)))))), inference(resolution, [status(thm)], [c_287, c_2])).
% 2.50/1.35  tff(c_325, plain, (![B_129, A_130]: (~v1_tops_2(B_129, A_130) | ~l1_pre_topc(A_130) | r1_tarski(B_129, u1_pre_topc(A_130)) | ~m1_subset_1(u1_pre_topc(A_130), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130)))) | ~m1_subset_1(B_129, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_130)))))), inference(resolution, [status(thm)], [c_319, c_295])).
% 2.50/1.35  tff(c_333, plain, (![B_134, A_135]: (~v1_tops_2(B_134, A_135) | r1_tarski(B_134, u1_pre_topc(A_135)) | ~m1_subset_1(B_134, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_135)))) | ~l1_pre_topc(A_135))), inference(resolution, [status(thm)], [c_12, c_325])).
% 2.50/1.35  tff(c_343, plain, (~v1_tops_2('#skF_4', '#skF_3') | r1_tarski('#skF_4', u1_pre_topc('#skF_3')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_333])).
% 2.50/1.35  tff(c_348, plain, (r1_tarski('#skF_4', u1_pre_topc('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_174, c_343])).
% 2.50/1.35  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_348])).
% 2.50/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  Inference rules
% 2.50/1.35  ----------------------
% 2.50/1.35  #Ref     : 0
% 2.50/1.35  #Sup     : 65
% 2.50/1.35  #Fact    : 0
% 2.50/1.35  #Define  : 0
% 2.50/1.35  #Split   : 1
% 2.50/1.35  #Chain   : 0
% 2.50/1.35  #Close   : 0
% 2.50/1.35  
% 2.50/1.35  Ordering : KBO
% 2.50/1.35  
% 2.50/1.35  Simplification rules
% 2.50/1.35  ----------------------
% 2.50/1.35  #Subsume      : 16
% 2.50/1.35  #Demod        : 12
% 2.50/1.35  #Tautology    : 13
% 2.50/1.35  #SimpNegUnit  : 6
% 2.50/1.35  #BackRed      : 0
% 2.50/1.35  
% 2.50/1.35  #Partial instantiations: 0
% 2.50/1.35  #Strategies tried      : 1
% 2.50/1.35  
% 2.50/1.35  Timing (in seconds)
% 2.50/1.35  ----------------------
% 2.50/1.35  Preprocessing        : 0.28
% 2.50/1.35  Parsing              : 0.15
% 2.50/1.35  CNF conversion       : 0.02
% 2.50/1.35  Main loop            : 0.29
% 2.50/1.35  Inferencing          : 0.12
% 2.50/1.35  Reduction            : 0.07
% 2.50/1.35  Demodulation         : 0.04
% 2.50/1.35  BG Simplification    : 0.02
% 2.50/1.35  Subsumption          : 0.06
% 2.50/1.35  Abstraction          : 0.01
% 2.50/1.35  MUC search           : 0.00
% 2.50/1.35  Cooper               : 0.00
% 2.50/1.35  Total                : 0.60
% 2.50/1.35  Index Insertion      : 0.00
% 2.50/1.35  Index Deletion       : 0.00
% 2.50/1.35  Index Matching       : 0.00
% 2.50/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
