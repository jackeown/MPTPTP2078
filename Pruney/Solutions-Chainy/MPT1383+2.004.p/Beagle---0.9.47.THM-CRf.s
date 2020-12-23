%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:11 EST 2020

% Result     : Theorem 6.05s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 497 expanded)
%              Number of leaves         :   27 ( 178 expanded)
%              Depth                    :   10
%              Number of atoms          :  461 (2115 expanded)
%              Number of equality atoms :   28 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( m1_connsp_2(C,A,B)
                <=> ? [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                      & v3_pre_topc(D,A)
                      & r1_tarski(D,C)
                      & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v3_pre_topc(B,A)
                  & r1_tarski(B,C) )
               => r1_tarski(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_53,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_55,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_52,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_71,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    ! [D_60] :
      ( ~ r2_hidden('#skF_3',D_60)
      | ~ r1_tarski(D_60,'#skF_4')
      | ~ v3_pre_topc(D_60,'#skF_2')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_281,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_28,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,(
    ! [A_63,B_64] :
      ( ~ r2_hidden('#skF_1'(A_63,B_64),B_64)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_596,plain,(
    ! [B_148,A_149,C_150] :
      ( r1_tarski(B_148,k1_tops_1(A_149,C_150))
      | ~ r1_tarski(B_148,C_150)
      | ~ v3_pre_topc(B_148,A_149)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_602,plain,(
    ! [B_148] :
      ( r1_tarski(B_148,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_148,'#skF_4')
      | ~ v3_pre_topc(B_148,'#skF_2')
      | ~ m1_subset_1(B_148,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_596])).

tff(c_610,plain,(
    ! [B_151] :
      ( r1_tarski(B_151,k1_tops_1('#skF_2','#skF_4'))
      | ~ r1_tarski(B_151,'#skF_4')
      | ~ v3_pre_topc(B_151,'#skF_2')
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_602])).

tff(c_617,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_610])).

tff(c_626,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_617])).

tff(c_64,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [B_69] :
      ( r2_hidden('#skF_3',B_69)
      | ~ r1_tarski('#skF_5',B_69) ) ),
    inference(resolution,[status(thm)],[c_54,c_64])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_75,plain,(
    ! [B_2,B_69] :
      ( r2_hidden('#skF_3',B_2)
      | ~ r1_tarski(B_69,B_2)
      | ~ r1_tarski('#skF_5',B_69) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_644,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_626,c_75])).

tff(c_654,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_644])).

tff(c_761,plain,(
    ! [C_164,A_165,B_166] :
      ( m1_connsp_2(C_164,A_165,B_166)
      | ~ r2_hidden(B_166,k1_tops_1(A_165,C_164))
      | ~ m1_subset_1(C_164,k1_zfmisc_1(u1_struct_0(A_165)))
      | ~ m1_subset_1(B_166,u1_struct_0(A_165))
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_768,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_654,c_761])).

tff(c_798,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_768])).

tff(c_800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_281,c_798])).

tff(c_803,plain,(
    ! [D_167] :
      ( ~ r2_hidden('#skF_3',D_167)
      | ~ r1_tarski(D_167,'#skF_4')
      | ~ v3_pre_topc(D_167,'#skF_2')
      | ~ m1_subset_1(D_167,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_810,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_803])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_54,c_810])).

tff(c_821,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1369,plain,(
    ! [B_258,A_259,C_260] :
      ( r2_hidden(B_258,k1_tops_1(A_259,C_260))
      | ~ m1_connsp_2(C_260,A_259,B_258)
      | ~ m1_subset_1(C_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | ~ m1_subset_1(B_258,u1_struct_0(A_259))
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1373,plain,(
    ! [B_258] :
      ( r2_hidden(B_258,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_258)
      | ~ m1_subset_1(B_258,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1369])).

tff(c_1377,plain,(
    ! [B_258] :
      ( r2_hidden(B_258,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_258)
      | ~ m1_subset_1(B_258,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1373])).

tff(c_1379,plain,(
    ! [B_261] :
      ( r2_hidden(B_261,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_261)
      | ~ m1_subset_1(B_261,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1377])).

tff(c_844,plain,(
    ! [A_172,B_173] :
      ( r1_tarski(k1_tops_1(A_172,B_173),B_173)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_846,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_844])).

tff(c_849,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_846])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1016,plain,(
    ! [D_209] :
      ( ~ r2_hidden('#skF_3',D_209)
      | ~ r1_tarski(D_209,'#skF_4')
      | ~ v3_pre_topc(D_209,'#skF_2')
      | ~ m1_subset_1(D_209,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_34])).

tff(c_1020,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1016])).

tff(c_1040,plain,(
    ! [B_212] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_212))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_212),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_212),'#skF_2')
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1020])).

tff(c_1047,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1040])).

tff(c_1053,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_1047])).

tff(c_1054,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1053])).

tff(c_915,plain,(
    ! [A_190,B_191] :
      ( k1_tops_1(A_190,k1_tops_1(A_190,B_191)) = k1_tops_1(A_190,B_191)
      | ~ m1_subset_1(B_191,k1_zfmisc_1(u1_struct_0(A_190)))
      | ~ l1_pre_topc(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_919,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_915])).

tff(c_923,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_919])).

tff(c_14,plain,(
    ! [C_25,A_13,D_27,B_21] :
      ( v3_pre_topc(C_25,A_13)
      | k1_tops_1(A_13,C_25) != C_25
      | ~ m1_subset_1(D_27,k1_zfmisc_1(u1_struct_0(B_21)))
      | ~ m1_subset_1(C_25,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(B_21)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1140,plain,(
    ! [D_226,B_227] :
      ( ~ m1_subset_1(D_226,k1_zfmisc_1(u1_struct_0(B_227)))
      | ~ l1_pre_topc(B_227) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_1143,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1140])).

tff(c_1147,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1143])).

tff(c_1149,plain,(
    ! [C_228,A_229] :
      ( v3_pre_topc(C_228,A_229)
      | k1_tops_1(A_229,C_228) != C_228
      | ~ m1_subset_1(C_228,k1_zfmisc_1(u1_struct_0(A_229)))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1161,plain,(
    ! [A_230,B_231] :
      ( v3_pre_topc(k1_tops_1(A_230,B_231),A_230)
      | k1_tops_1(A_230,k1_tops_1(A_230,B_231)) != k1_tops_1(A_230,B_231)
      | ~ v2_pre_topc(A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(resolution,[status(thm)],[c_8,c_1149])).

tff(c_1165,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1161])).

tff(c_1169,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_923,c_1165])).

tff(c_1171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1054,c_1169])).

tff(c_1172,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1053])).

tff(c_1382,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1379,c_1172])).

tff(c_1392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_821,c_1382])).

tff(c_1393,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1975,plain,(
    ! [B_351,A_352,C_353] :
      ( r2_hidden(B_351,k1_tops_1(A_352,C_353))
      | ~ m1_connsp_2(C_353,A_352,B_351)
      | ~ m1_subset_1(C_353,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ m1_subset_1(B_351,u1_struct_0(A_352))
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1979,plain,(
    ! [B_351] :
      ( r2_hidden(B_351,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_351)
      | ~ m1_subset_1(B_351,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1975])).

tff(c_1983,plain,(
    ! [B_351] :
      ( r2_hidden(B_351,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_351)
      | ~ m1_subset_1(B_351,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1979])).

tff(c_1985,plain,(
    ! [B_354] :
      ( r2_hidden(B_354,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_354)
      | ~ m1_subset_1(B_354,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1983])).

tff(c_1415,plain,(
    ! [A_271,B_272] :
      ( r1_tarski(k1_tops_1(A_271,B_272),B_272)
      | ~ m1_subset_1(B_272,k1_zfmisc_1(u1_struct_0(A_271)))
      | ~ l1_pre_topc(A_271) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1417,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1415])).

tff(c_1420,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1417])).

tff(c_1394,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_42,plain,(
    ! [D_60] :
      ( ~ r2_hidden('#skF_3',D_60)
      | ~ r1_tarski(D_60,'#skF_4')
      | ~ v3_pre_topc(D_60,'#skF_2')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1529,plain,(
    ! [D_296] :
      ( ~ r2_hidden('#skF_3',D_296)
      | ~ r1_tarski(D_296,'#skF_4')
      | ~ v3_pre_topc(D_296,'#skF_2')
      | ~ m1_subset_1(D_296,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1394,c_42])).

tff(c_1533,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1529])).

tff(c_1566,plain,(
    ! [B_301] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_301))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_301),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_301),'#skF_2')
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1533])).

tff(c_1573,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1566])).

tff(c_1579,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_1573])).

tff(c_1580,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1579])).

tff(c_1459,plain,(
    ! [A_286,B_287] :
      ( k1_tops_1(A_286,k1_tops_1(A_286,B_287)) = k1_tops_1(A_286,B_287)
      | ~ m1_subset_1(B_287,k1_zfmisc_1(u1_struct_0(A_286)))
      | ~ l1_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1463,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1459])).

tff(c_1467,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1463])).

tff(c_1674,plain,(
    ! [D_316,B_317] :
      ( ~ m1_subset_1(D_316,k1_zfmisc_1(u1_struct_0(B_317)))
      | ~ l1_pre_topc(B_317) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_1677,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1674])).

tff(c_1681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1677])).

tff(c_1683,plain,(
    ! [C_318,A_319] :
      ( v3_pre_topc(C_318,A_319)
      | k1_tops_1(A_319,C_318) != C_318
      | ~ m1_subset_1(C_318,k1_zfmisc_1(u1_struct_0(A_319)))
      | ~ l1_pre_topc(A_319)
      | ~ v2_pre_topc(A_319) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_1717,plain,(
    ! [A_323,B_324] :
      ( v3_pre_topc(k1_tops_1(A_323,B_324),A_323)
      | k1_tops_1(A_323,k1_tops_1(A_323,B_324)) != k1_tops_1(A_323,B_324)
      | ~ v2_pre_topc(A_323)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0(A_323)))
      | ~ l1_pre_topc(A_323) ) ),
    inference(resolution,[status(thm)],[c_8,c_1683])).

tff(c_1721,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1717])).

tff(c_1725,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_1467,c_1721])).

tff(c_1727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1580,c_1725])).

tff(c_1728,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1579])).

tff(c_1990,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1985,c_1728])).

tff(c_2004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1393,c_1990])).

tff(c_2005,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2442,plain,(
    ! [B_421,A_422,C_423] :
      ( r2_hidden(B_421,k1_tops_1(A_422,C_423))
      | ~ m1_connsp_2(C_423,A_422,B_421)
      | ~ m1_subset_1(C_423,k1_zfmisc_1(u1_struct_0(A_422)))
      | ~ m1_subset_1(B_421,u1_struct_0(A_422))
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2448,plain,(
    ! [B_421] :
      ( r2_hidden(B_421,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_421)
      | ~ m1_subset_1(B_421,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_2442])).

tff(c_2456,plain,(
    ! [B_421] :
      ( r2_hidden(B_421,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_421)
      | ~ m1_subset_1(B_421,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2448])).

tff(c_2458,plain,(
    ! [B_424] :
      ( r2_hidden(B_424,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_424)
      | ~ m1_subset_1(B_424,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2456])).

tff(c_2021,plain,(
    ! [A_363,B_364] :
      ( r1_tarski(k1_tops_1(A_363,B_364),B_364)
      | ~ m1_subset_1(B_364,k1_zfmisc_1(u1_struct_0(A_363)))
      | ~ l1_pre_topc(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2023,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2021])).

tff(c_2026,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2023])).

tff(c_2006,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,(
    ! [D_60] :
      ( ~ r2_hidden('#skF_3',D_60)
      | ~ r1_tarski(D_60,'#skF_4')
      | ~ v3_pre_topc(D_60,'#skF_2')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2041,plain,(
    ! [D_370] :
      ( ~ r2_hidden('#skF_3',D_370)
      | ~ r1_tarski(D_370,'#skF_4')
      | ~ v3_pre_topc(D_370,'#skF_2')
      | ~ m1_subset_1(D_370,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2006,c_38])).

tff(c_2045,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_2041])).

tff(c_2171,plain,(
    ! [B_393] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_393))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_393),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_393),'#skF_2')
      | ~ m1_subset_1(B_393,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2045])).

tff(c_2178,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2171])).

tff(c_2184,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_2178])).

tff(c_2185,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2184])).

tff(c_2079,plain,(
    ! [A_378,B_379] :
      ( k1_tops_1(A_378,k1_tops_1(A_378,B_379)) = k1_tops_1(A_378,B_379)
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2083,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2079])).

tff(c_2087,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2083])).

tff(c_2150,plain,(
    ! [D_389,B_390] :
      ( ~ m1_subset_1(D_389,k1_zfmisc_1(u1_struct_0(B_390)))
      | ~ l1_pre_topc(B_390) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_2153,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2150])).

tff(c_2157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2153])).

tff(c_2159,plain,(
    ! [C_391,A_392] :
      ( v3_pre_topc(C_391,A_392)
      | k1_tops_1(A_392,C_391) != C_391
      | ~ m1_subset_1(C_391,k1_zfmisc_1(u1_struct_0(A_392)))
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_2196,plain,(
    ! [A_398,B_399] :
      ( v3_pre_topc(k1_tops_1(A_398,B_399),A_398)
      | k1_tops_1(A_398,k1_tops_1(A_398,B_399)) != k1_tops_1(A_398,B_399)
      | ~ v2_pre_topc(A_398)
      | ~ m1_subset_1(B_399,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398) ) ),
    inference(resolution,[status(thm)],[c_8,c_2159])).

tff(c_2200,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2196])).

tff(c_2204,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2087,c_2200])).

tff(c_2206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2185,c_2204])).

tff(c_2207,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2184])).

tff(c_2463,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2458,c_2207])).

tff(c_2477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2005,c_2463])).

tff(c_2478,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_3991,plain,(
    ! [B_642,A_643,C_644] :
      ( r2_hidden(B_642,k1_tops_1(A_643,C_644))
      | ~ m1_connsp_2(C_644,A_643,B_642)
      | ~ m1_subset_1(C_644,k1_zfmisc_1(u1_struct_0(A_643)))
      | ~ m1_subset_1(B_642,u1_struct_0(A_643))
      | ~ l1_pre_topc(A_643)
      | ~ v2_pre_topc(A_643)
      | v2_struct_0(A_643) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_3995,plain,(
    ! [B_642] :
      ( r2_hidden(B_642,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_642)
      | ~ m1_subset_1(B_642,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_3991])).

tff(c_3999,plain,(
    ! [B_642] :
      ( r2_hidden(B_642,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_642)
      | ~ m1_subset_1(B_642,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_3995])).

tff(c_4001,plain,(
    ! [B_645] :
      ( r2_hidden(B_645,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_645)
      | ~ m1_subset_1(B_645,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3999])).

tff(c_2504,plain,(
    ! [A_436,B_437] :
      ( r1_tarski(k1_tops_1(A_436,B_437),B_437)
      | ~ m1_subset_1(B_437,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2506,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2504])).

tff(c_2509,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2506])).

tff(c_2479,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,(
    ! [D_60] :
      ( ~ r2_hidden('#skF_3',D_60)
      | ~ r1_tarski(D_60,'#skF_4')
      | ~ v3_pre_topc(D_60,'#skF_2')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3410,plain,(
    ! [D_558] :
      ( ~ r2_hidden('#skF_3',D_558)
      | ~ r1_tarski(D_558,'#skF_4')
      | ~ v3_pre_topc(D_558,'#skF_2')
      | ~ m1_subset_1(D_558,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2479,c_46])).

tff(c_3414,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_3410])).

tff(c_3519,plain,(
    ! [B_575] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_575))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_575),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_575),'#skF_2')
      | ~ m1_subset_1(B_575,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3414])).

tff(c_3526,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3519])).

tff(c_3532,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2509,c_3526])).

tff(c_3533,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3532])).

tff(c_2953,plain,(
    ! [A_500,B_501] :
      ( k1_tops_1(A_500,k1_tops_1(A_500,B_501)) = k1_tops_1(A_500,B_501)
      | ~ m1_subset_1(B_501,k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ l1_pre_topc(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2957,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2953])).

tff(c_2961,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2957])).

tff(c_3670,plain,(
    ! [D_601,B_602] :
      ( ~ m1_subset_1(D_601,k1_zfmisc_1(u1_struct_0(B_602)))
      | ~ l1_pre_topc(B_602) ) ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_3673,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3670])).

tff(c_3677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_3673])).

tff(c_3679,plain,(
    ! [C_603,A_604] :
      ( v3_pre_topc(C_603,A_604)
      | k1_tops_1(A_604,C_603) != C_603
      | ~ m1_subset_1(C_603,k1_zfmisc_1(u1_struct_0(A_604)))
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604) ) ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_3691,plain,(
    ! [A_605,B_606] :
      ( v3_pre_topc(k1_tops_1(A_605,B_606),A_605)
      | k1_tops_1(A_605,k1_tops_1(A_605,B_606)) != k1_tops_1(A_605,B_606)
      | ~ v2_pre_topc(A_605)
      | ~ m1_subset_1(B_606,k1_zfmisc_1(u1_struct_0(A_605)))
      | ~ l1_pre_topc(A_605) ) ),
    inference(resolution,[status(thm)],[c_8,c_3679])).

tff(c_3695,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) != k1_tops_1('#skF_2','#skF_4')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_3691])).

tff(c_3699,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_2961,c_3695])).

tff(c_3701,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3533,c_3699])).

tff(c_3702,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3532])).

tff(c_4004,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4001,c_3702])).

tff(c_4014,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2478,c_4004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:09:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.05/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.23  
% 6.47/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.24  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.47/2.24  
% 6.47/2.24  %Foreground sorts:
% 6.47/2.24  
% 6.47/2.24  
% 6.47/2.24  %Background operators:
% 6.47/2.24  
% 6.47/2.24  
% 6.47/2.24  %Foreground operators:
% 6.47/2.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.47/2.24  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.47/2.24  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.47/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.24  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.47/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.24  tff('#skF_5', type, '#skF_5': $i).
% 6.47/2.24  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.47/2.24  tff('#skF_2', type, '#skF_2': $i).
% 6.47/2.24  tff('#skF_3', type, '#skF_3': $i).
% 6.47/2.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.47/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.24  tff('#skF_4', type, '#skF_4': $i).
% 6.47/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.24  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.47/2.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.47/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.47/2.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.47/2.24  
% 6.47/2.27  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 6.47/2.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.47/2.27  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & r1_tarski(B, C)) => r1_tarski(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_tops_1)).
% 6.47/2.27  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 6.47/2.27  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.47/2.27  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.47/2.27  tff(f_44, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 6.47/2.27  tff(f_72, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 6.47/2.27  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_48, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_53, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 6.47/2.27  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_55, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 6.47/2.27  tff(c_40, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 6.47/2.27  tff(c_52, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_71, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_52])).
% 6.47/2.27  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_34, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_281, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 6.47/2.27  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.47/2.27  tff(c_57, plain, (![A_63, B_64]: (~r2_hidden('#skF_1'(A_63, B_64), B_64) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.47/2.27  tff(c_62, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_57])).
% 6.47/2.27  tff(c_596, plain, (![B_148, A_149, C_150]: (r1_tarski(B_148, k1_tops_1(A_149, C_150)) | ~r1_tarski(B_148, C_150) | ~v3_pre_topc(B_148, A_149) | ~m1_subset_1(C_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.47/2.27  tff(c_602, plain, (![B_148]: (r1_tarski(B_148, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_148, '#skF_4') | ~v3_pre_topc(B_148, '#skF_2') | ~m1_subset_1(B_148, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_596])).
% 6.47/2.27  tff(c_610, plain, (![B_151]: (r1_tarski(B_151, k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(B_151, '#skF_4') | ~v3_pre_topc(B_151, '#skF_2') | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_602])).
% 6.47/2.27  tff(c_617, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_71, c_610])).
% 6.47/2.27  tff(c_626, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_617])).
% 6.47/2.27  tff(c_64, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.47/2.27  tff(c_72, plain, (![B_69]: (r2_hidden('#skF_3', B_69) | ~r1_tarski('#skF_5', B_69))), inference(resolution, [status(thm)], [c_54, c_64])).
% 6.47/2.27  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.47/2.27  tff(c_75, plain, (![B_2, B_69]: (r2_hidden('#skF_3', B_2) | ~r1_tarski(B_69, B_2) | ~r1_tarski('#skF_5', B_69))), inference(resolution, [status(thm)], [c_72, c_2])).
% 6.47/2.27  tff(c_644, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_626, c_75])).
% 6.47/2.27  tff(c_654, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_644])).
% 6.47/2.27  tff(c_761, plain, (![C_164, A_165, B_166]: (m1_connsp_2(C_164, A_165, B_166) | ~r2_hidden(B_166, k1_tops_1(A_165, C_164)) | ~m1_subset_1(C_164, k1_zfmisc_1(u1_struct_0(A_165))) | ~m1_subset_1(B_166, u1_struct_0(A_165)) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.47/2.27  tff(c_768, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_654, c_761])).
% 6.47/2.27  tff(c_798, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_768])).
% 6.47/2.27  tff(c_800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_281, c_798])).
% 6.47/2.27  tff(c_803, plain, (![D_167]: (~r2_hidden('#skF_3', D_167) | ~r1_tarski(D_167, '#skF_4') | ~v3_pre_topc(D_167, '#skF_2') | ~m1_subset_1(D_167, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_34])).
% 6.47/2.27  tff(c_810, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_71, c_803])).
% 6.47/2.27  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_54, c_810])).
% 6.47/2.27  tff(c_821, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 6.47/2.27  tff(c_1369, plain, (![B_258, A_259, C_260]: (r2_hidden(B_258, k1_tops_1(A_259, C_260)) | ~m1_connsp_2(C_260, A_259, B_258) | ~m1_subset_1(C_260, k1_zfmisc_1(u1_struct_0(A_259))) | ~m1_subset_1(B_258, u1_struct_0(A_259)) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.47/2.27  tff(c_1373, plain, (![B_258]: (r2_hidden(B_258, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_258) | ~m1_subset_1(B_258, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1369])).
% 6.47/2.27  tff(c_1377, plain, (![B_258]: (r2_hidden(B_258, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_258) | ~m1_subset_1(B_258, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1373])).
% 6.47/2.27  tff(c_1379, plain, (![B_261]: (r2_hidden(B_261, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_261) | ~m1_subset_1(B_261, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1377])).
% 6.47/2.27  tff(c_844, plain, (![A_172, B_173]: (r1_tarski(k1_tops_1(A_172, B_173), B_173) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.47/2.27  tff(c_846, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_844])).
% 6.47/2.27  tff(c_849, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_846])).
% 6.47/2.27  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.47/2.27  tff(c_1016, plain, (![D_209]: (~r2_hidden('#skF_3', D_209) | ~r1_tarski(D_209, '#skF_4') | ~v3_pre_topc(D_209, '#skF_2') | ~m1_subset_1(D_209, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_34])).
% 6.47/2.27  tff(c_1020, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1016])).
% 6.47/2.27  tff(c_1040, plain, (![B_212]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_212)) | ~r1_tarski(k1_tops_1('#skF_2', B_212), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_212), '#skF_2') | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1020])).
% 6.47/2.27  tff(c_1047, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_1040])).
% 6.47/2.27  tff(c_1053, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_849, c_1047])).
% 6.47/2.27  tff(c_1054, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1053])).
% 6.47/2.27  tff(c_915, plain, (![A_190, B_191]: (k1_tops_1(A_190, k1_tops_1(A_190, B_191))=k1_tops_1(A_190, B_191) | ~m1_subset_1(B_191, k1_zfmisc_1(u1_struct_0(A_190))) | ~l1_pre_topc(A_190))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.47/2.27  tff(c_919, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_915])).
% 6.47/2.27  tff(c_923, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_919])).
% 6.47/2.27  tff(c_14, plain, (![C_25, A_13, D_27, B_21]: (v3_pre_topc(C_25, A_13) | k1_tops_1(A_13, C_25)!=C_25 | ~m1_subset_1(D_27, k1_zfmisc_1(u1_struct_0(B_21))) | ~m1_subset_1(C_25, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(B_21) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.47/2.27  tff(c_1140, plain, (![D_226, B_227]: (~m1_subset_1(D_226, k1_zfmisc_1(u1_struct_0(B_227))) | ~l1_pre_topc(B_227))), inference(splitLeft, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_1143, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1140])).
% 6.47/2.27  tff(c_1147, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1143])).
% 6.47/2.27  tff(c_1149, plain, (![C_228, A_229]: (v3_pre_topc(C_228, A_229) | k1_tops_1(A_229, C_228)!=C_228 | ~m1_subset_1(C_228, k1_zfmisc_1(u1_struct_0(A_229))) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229))), inference(splitRight, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_1161, plain, (![A_230, B_231]: (v3_pre_topc(k1_tops_1(A_230, B_231), A_230) | k1_tops_1(A_230, k1_tops_1(A_230, B_231))!=k1_tops_1(A_230, B_231) | ~v2_pre_topc(A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(resolution, [status(thm)], [c_8, c_1149])).
% 6.47/2.27  tff(c_1165, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))!=k1_tops_1('#skF_2', '#skF_4') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1161])).
% 6.47/2.27  tff(c_1169, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_923, c_1165])).
% 6.47/2.27  tff(c_1171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1054, c_1169])).
% 6.47/2.27  tff(c_1172, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_1053])).
% 6.47/2.27  tff(c_1382, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1379, c_1172])).
% 6.47/2.27  tff(c_1392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_821, c_1382])).
% 6.47/2.27  tff(c_1393, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 6.47/2.27  tff(c_1975, plain, (![B_351, A_352, C_353]: (r2_hidden(B_351, k1_tops_1(A_352, C_353)) | ~m1_connsp_2(C_353, A_352, B_351) | ~m1_subset_1(C_353, k1_zfmisc_1(u1_struct_0(A_352))) | ~m1_subset_1(B_351, u1_struct_0(A_352)) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.47/2.27  tff(c_1979, plain, (![B_351]: (r2_hidden(B_351, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_351) | ~m1_subset_1(B_351, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1975])).
% 6.47/2.27  tff(c_1983, plain, (![B_351]: (r2_hidden(B_351, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_351) | ~m1_subset_1(B_351, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1979])).
% 6.47/2.27  tff(c_1985, plain, (![B_354]: (r2_hidden(B_354, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_354) | ~m1_subset_1(B_354, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1983])).
% 6.47/2.27  tff(c_1415, plain, (![A_271, B_272]: (r1_tarski(k1_tops_1(A_271, B_272), B_272) | ~m1_subset_1(B_272, k1_zfmisc_1(u1_struct_0(A_271))) | ~l1_pre_topc(A_271))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.47/2.27  tff(c_1417, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1415])).
% 6.47/2.27  tff(c_1420, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1417])).
% 6.47/2.27  tff(c_1394, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 6.47/2.27  tff(c_42, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_1529, plain, (![D_296]: (~r2_hidden('#skF_3', D_296) | ~r1_tarski(D_296, '#skF_4') | ~v3_pre_topc(D_296, '#skF_2') | ~m1_subset_1(D_296, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1394, c_42])).
% 6.47/2.27  tff(c_1533, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1529])).
% 6.47/2.27  tff(c_1566, plain, (![B_301]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_301)) | ~r1_tarski(k1_tops_1('#skF_2', B_301), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_301), '#skF_2') | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1533])).
% 6.47/2.27  tff(c_1573, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_1566])).
% 6.47/2.27  tff(c_1579, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_1573])).
% 6.47/2.27  tff(c_1580, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1579])).
% 6.47/2.27  tff(c_1459, plain, (![A_286, B_287]: (k1_tops_1(A_286, k1_tops_1(A_286, B_287))=k1_tops_1(A_286, B_287) | ~m1_subset_1(B_287, k1_zfmisc_1(u1_struct_0(A_286))) | ~l1_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.47/2.27  tff(c_1463, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1459])).
% 6.47/2.27  tff(c_1467, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1463])).
% 6.47/2.27  tff(c_1674, plain, (![D_316, B_317]: (~m1_subset_1(D_316, k1_zfmisc_1(u1_struct_0(B_317))) | ~l1_pre_topc(B_317))), inference(splitLeft, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_1677, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1674])).
% 6.47/2.27  tff(c_1681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_1677])).
% 6.47/2.27  tff(c_1683, plain, (![C_318, A_319]: (v3_pre_topc(C_318, A_319) | k1_tops_1(A_319, C_318)!=C_318 | ~m1_subset_1(C_318, k1_zfmisc_1(u1_struct_0(A_319))) | ~l1_pre_topc(A_319) | ~v2_pre_topc(A_319))), inference(splitRight, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_1717, plain, (![A_323, B_324]: (v3_pre_topc(k1_tops_1(A_323, B_324), A_323) | k1_tops_1(A_323, k1_tops_1(A_323, B_324))!=k1_tops_1(A_323, B_324) | ~v2_pre_topc(A_323) | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0(A_323))) | ~l1_pre_topc(A_323))), inference(resolution, [status(thm)], [c_8, c_1683])).
% 6.47/2.27  tff(c_1721, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))!=k1_tops_1('#skF_2', '#skF_4') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1717])).
% 6.47/2.27  tff(c_1725, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_1467, c_1721])).
% 6.47/2.27  tff(c_1727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1580, c_1725])).
% 6.47/2.27  tff(c_1728, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_1579])).
% 6.47/2.27  tff(c_1990, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1985, c_1728])).
% 6.47/2.27  tff(c_2004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1393, c_1990])).
% 6.47/2.27  tff(c_2005, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 6.47/2.27  tff(c_2442, plain, (![B_421, A_422, C_423]: (r2_hidden(B_421, k1_tops_1(A_422, C_423)) | ~m1_connsp_2(C_423, A_422, B_421) | ~m1_subset_1(C_423, k1_zfmisc_1(u1_struct_0(A_422))) | ~m1_subset_1(B_421, u1_struct_0(A_422)) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.47/2.27  tff(c_2448, plain, (![B_421]: (r2_hidden(B_421, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_421) | ~m1_subset_1(B_421, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2442])).
% 6.47/2.27  tff(c_2456, plain, (![B_421]: (r2_hidden(B_421, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_421) | ~m1_subset_1(B_421, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2448])).
% 6.47/2.27  tff(c_2458, plain, (![B_424]: (r2_hidden(B_424, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_424) | ~m1_subset_1(B_424, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2456])).
% 6.47/2.27  tff(c_2021, plain, (![A_363, B_364]: (r1_tarski(k1_tops_1(A_363, B_364), B_364) | ~m1_subset_1(B_364, k1_zfmisc_1(u1_struct_0(A_363))) | ~l1_pre_topc(A_363))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.47/2.27  tff(c_2023, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2021])).
% 6.47/2.27  tff(c_2026, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2023])).
% 6.47/2.27  tff(c_2006, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 6.47/2.27  tff(c_38, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_2041, plain, (![D_370]: (~r2_hidden('#skF_3', D_370) | ~r1_tarski(D_370, '#skF_4') | ~v3_pre_topc(D_370, '#skF_2') | ~m1_subset_1(D_370, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2006, c_38])).
% 6.47/2.27  tff(c_2045, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_2041])).
% 6.47/2.27  tff(c_2171, plain, (![B_393]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_393)) | ~r1_tarski(k1_tops_1('#skF_2', B_393), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_393), '#skF_2') | ~m1_subset_1(B_393, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2045])).
% 6.47/2.27  tff(c_2178, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_2171])).
% 6.47/2.27  tff(c_2184, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_2178])).
% 6.47/2.27  tff(c_2185, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2184])).
% 6.47/2.27  tff(c_2079, plain, (![A_378, B_379]: (k1_tops_1(A_378, k1_tops_1(A_378, B_379))=k1_tops_1(A_378, B_379) | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.47/2.27  tff(c_2083, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2079])).
% 6.47/2.27  tff(c_2087, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2083])).
% 6.47/2.27  tff(c_2150, plain, (![D_389, B_390]: (~m1_subset_1(D_389, k1_zfmisc_1(u1_struct_0(B_390))) | ~l1_pre_topc(B_390))), inference(splitLeft, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_2153, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2150])).
% 6.47/2.27  tff(c_2157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2153])).
% 6.47/2.27  tff(c_2159, plain, (![C_391, A_392]: (v3_pre_topc(C_391, A_392) | k1_tops_1(A_392, C_391)!=C_391 | ~m1_subset_1(C_391, k1_zfmisc_1(u1_struct_0(A_392))) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392))), inference(splitRight, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_2196, plain, (![A_398, B_399]: (v3_pre_topc(k1_tops_1(A_398, B_399), A_398) | k1_tops_1(A_398, k1_tops_1(A_398, B_399))!=k1_tops_1(A_398, B_399) | ~v2_pre_topc(A_398) | ~m1_subset_1(B_399, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398))), inference(resolution, [status(thm)], [c_8, c_2159])).
% 6.47/2.27  tff(c_2200, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))!=k1_tops_1('#skF_2', '#skF_4') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2196])).
% 6.47/2.27  tff(c_2204, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2087, c_2200])).
% 6.47/2.27  tff(c_2206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2185, c_2204])).
% 6.47/2.27  tff(c_2207, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_2184])).
% 6.47/2.27  tff(c_2463, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2458, c_2207])).
% 6.47/2.27  tff(c_2477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2005, c_2463])).
% 6.47/2.27  tff(c_2478, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.47/2.27  tff(c_3991, plain, (![B_642, A_643, C_644]: (r2_hidden(B_642, k1_tops_1(A_643, C_644)) | ~m1_connsp_2(C_644, A_643, B_642) | ~m1_subset_1(C_644, k1_zfmisc_1(u1_struct_0(A_643))) | ~m1_subset_1(B_642, u1_struct_0(A_643)) | ~l1_pre_topc(A_643) | ~v2_pre_topc(A_643) | v2_struct_0(A_643))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.47/2.27  tff(c_3995, plain, (![B_642]: (r2_hidden(B_642, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_642) | ~m1_subset_1(B_642, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_3991])).
% 6.47/2.27  tff(c_3999, plain, (![B_642]: (r2_hidden(B_642, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_642) | ~m1_subset_1(B_642, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_3995])).
% 6.47/2.27  tff(c_4001, plain, (![B_645]: (r2_hidden(B_645, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_645) | ~m1_subset_1(B_645, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_3999])).
% 6.47/2.27  tff(c_2504, plain, (![A_436, B_437]: (r1_tarski(k1_tops_1(A_436, B_437), B_437) | ~m1_subset_1(B_437, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.47/2.27  tff(c_2506, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2504])).
% 6.47/2.27  tff(c_2509, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2506])).
% 6.47/2.27  tff(c_2479, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.47/2.27  tff(c_46, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.47/2.27  tff(c_3410, plain, (![D_558]: (~r2_hidden('#skF_3', D_558) | ~r1_tarski(D_558, '#skF_4') | ~v3_pre_topc(D_558, '#skF_2') | ~m1_subset_1(D_558, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2479, c_46])).
% 6.47/2.27  tff(c_3414, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_3410])).
% 6.47/2.27  tff(c_3519, plain, (![B_575]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_575)) | ~r1_tarski(k1_tops_1('#skF_2', B_575), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_575), '#skF_2') | ~m1_subset_1(B_575, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_3414])).
% 6.47/2.27  tff(c_3526, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_3519])).
% 6.47/2.27  tff(c_3532, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2509, c_3526])).
% 6.47/2.27  tff(c_3533, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_3532])).
% 6.47/2.27  tff(c_2953, plain, (![A_500, B_501]: (k1_tops_1(A_500, k1_tops_1(A_500, B_501))=k1_tops_1(A_500, B_501) | ~m1_subset_1(B_501, k1_zfmisc_1(u1_struct_0(A_500))) | ~l1_pre_topc(A_500))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.47/2.27  tff(c_2957, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2953])).
% 6.47/2.27  tff(c_2961, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2957])).
% 6.47/2.27  tff(c_3670, plain, (![D_601, B_602]: (~m1_subset_1(D_601, k1_zfmisc_1(u1_struct_0(B_602))) | ~l1_pre_topc(B_602))), inference(splitLeft, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_3673, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3670])).
% 6.47/2.27  tff(c_3677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_3673])).
% 6.47/2.27  tff(c_3679, plain, (![C_603, A_604]: (v3_pre_topc(C_603, A_604) | k1_tops_1(A_604, C_603)!=C_603 | ~m1_subset_1(C_603, k1_zfmisc_1(u1_struct_0(A_604))) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604))), inference(splitRight, [status(thm)], [c_14])).
% 6.47/2.27  tff(c_3691, plain, (![A_605, B_606]: (v3_pre_topc(k1_tops_1(A_605, B_606), A_605) | k1_tops_1(A_605, k1_tops_1(A_605, B_606))!=k1_tops_1(A_605, B_606) | ~v2_pre_topc(A_605) | ~m1_subset_1(B_606, k1_zfmisc_1(u1_struct_0(A_605))) | ~l1_pre_topc(A_605))), inference(resolution, [status(thm)], [c_8, c_3679])).
% 6.47/2.27  tff(c_3695, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))!=k1_tops_1('#skF_2', '#skF_4') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_3691])).
% 6.47/2.27  tff(c_3699, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_2961, c_3695])).
% 6.47/2.27  tff(c_3701, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3533, c_3699])).
% 6.47/2.27  tff(c_3702, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_3532])).
% 6.47/2.27  tff(c_4004, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4001, c_3702])).
% 6.47/2.27  tff(c_4014, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2478, c_4004])).
% 6.47/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.27  
% 6.47/2.27  Inference rules
% 6.47/2.27  ----------------------
% 6.47/2.27  #Ref     : 0
% 6.47/2.27  #Sup     : 806
% 6.47/2.27  #Fact    : 0
% 6.47/2.27  #Define  : 0
% 6.47/2.27  #Split   : 45
% 6.47/2.27  #Chain   : 0
% 6.47/2.27  #Close   : 0
% 6.47/2.27  
% 6.47/2.27  Ordering : KBO
% 6.47/2.27  
% 6.47/2.27  Simplification rules
% 6.47/2.27  ----------------------
% 6.47/2.27  #Subsume      : 312
% 6.47/2.27  #Demod        : 751
% 6.47/2.27  #Tautology    : 224
% 6.47/2.27  #SimpNegUnit  : 57
% 6.47/2.27  #BackRed      : 10
% 6.47/2.27  
% 6.47/2.27  #Partial instantiations: 0
% 6.47/2.27  #Strategies tried      : 1
% 6.47/2.27  
% 6.47/2.27  Timing (in seconds)
% 6.47/2.27  ----------------------
% 6.47/2.27  Preprocessing        : 0.31
% 6.47/2.27  Parsing              : 0.18
% 6.47/2.27  CNF conversion       : 0.02
% 6.47/2.27  Main loop            : 1.13
% 6.47/2.27  Inferencing          : 0.41
% 6.47/2.27  Reduction            : 0.34
% 6.47/2.27  Demodulation         : 0.23
% 6.47/2.27  BG Simplification    : 0.04
% 6.47/2.27  Subsumption          : 0.28
% 6.47/2.27  Abstraction          : 0.05
% 6.47/2.27  MUC search           : 0.00
% 6.47/2.27  Cooper               : 0.00
% 6.47/2.27  Total                : 1.52
% 6.47/2.27  Index Insertion      : 0.00
% 6.47/2.27  Index Deletion       : 0.00
% 6.47/2.27  Index Matching       : 0.00
% 6.47/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
