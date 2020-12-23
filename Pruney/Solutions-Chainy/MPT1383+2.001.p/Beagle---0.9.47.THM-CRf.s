%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:11 EST 2020

% Result     : Theorem 5.96s
% Output     : CNFRefutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 327 expanded)
%              Number of leaves         :   27 ( 125 expanded)
%              Depth                    :   13
%              Number of atoms          :  394 (1388 expanded)
%              Number of equality atoms :    6 (   9 expanded)
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

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

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_53,axiom,(
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

tff(c_217,plain,(
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

tff(c_18,plain,(
    ! [B_28,D_34,C_32,A_20] :
      ( k1_tops_1(B_28,D_34) = D_34
      | ~ v3_pre_topc(D_34,B_28)
      | ~ m1_subset_1(D_34,k1_zfmisc_1(u1_struct_0(B_28)))
      | ~ m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(B_28)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_567,plain,(
    ! [C_140,A_141] :
      ( ~ m1_subset_1(C_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141) ) ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_573,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_567])).

tff(c_581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_573])).

tff(c_588,plain,(
    ! [B_144,D_145] :
      ( k1_tops_1(B_144,D_145) = D_145
      | ~ v3_pre_topc(D_145,B_144)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(u1_struct_0(B_144)))
      | ~ l1_pre_topc(B_144) ) ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_594,plain,
    ( k1_tops_1('#skF_2','#skF_5') = '#skF_5'
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_588])).

tff(c_601,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_53,c_594])).

tff(c_14,plain,(
    ! [A_13,B_17,C_19] :
      ( r1_tarski(k1_tops_1(A_13,B_17),k1_tops_1(A_13,C_19))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_630,plain,(
    ! [C_19] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_19))
      | ~ r1_tarski('#skF_5',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_14])).

tff(c_669,plain,(
    ! [C_148] :
      ( r1_tarski('#skF_5',k1_tops_1('#skF_2',C_148))
      | ~ r1_tarski('#skF_5',C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_71,c_630])).

tff(c_679,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_669])).

tff(c_688,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_679])).

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

tff(c_699,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_688,c_75])).

tff(c_707,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_699])).

tff(c_858,plain,(
    ! [C_165,A_166,B_167] :
      ( m1_connsp_2(C_165,A_166,B_167)
      | ~ r2_hidden(B_167,k1_tops_1(A_166,C_165))
      | ~ m1_subset_1(C_165,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_867,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_707,c_858])).

tff(c_899,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_867])).

tff(c_901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_217,c_899])).

tff(c_937,plain,(
    ! [D_174] :
      ( ~ r2_hidden('#skF_3',D_174)
      | ~ r1_tarski(D_174,'#skF_4')
      | ~ v3_pre_topc(D_174,'#skF_2')
      | ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_944,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_71,c_937])).

tff(c_954,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_55,c_54,c_944])).

tff(c_955,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1704,plain,(
    ! [B_271,A_272,C_273] :
      ( r2_hidden(B_271,k1_tops_1(A_272,C_273))
      | ~ m1_connsp_2(C_273,A_272,B_271)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ m1_subset_1(B_271,u1_struct_0(A_272))
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1710,plain,(
    ! [B_271] :
      ( r2_hidden(B_271,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_271)
      | ~ m1_subset_1(B_271,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_1704])).

tff(c_1718,plain,(
    ! [B_271] :
      ( r2_hidden(B_271,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_271)
      | ~ m1_subset_1(B_271,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1710])).

tff(c_1720,plain,(
    ! [B_274] :
      ( r2_hidden(B_274,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_274)
      | ~ m1_subset_1(B_274,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1718])).

tff(c_1013,plain,(
    ! [A_188,B_189] :
      ( v3_pre_topc(k1_tops_1(A_188,B_189),A_188)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188)
      | ~ v2_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1017,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1013])).

tff(c_1021,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1017])).

tff(c_957,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k1_tops_1(A_175,B_176),B_176)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(u1_struct_0(A_175)))
      | ~ l1_pre_topc(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_959,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_957])).

tff(c_962,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_959])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1100,plain,(
    ! [D_209] :
      ( ~ r2_hidden('#skF_3',D_209)
      | ~ r1_tarski(D_209,'#skF_4')
      | ~ v3_pre_topc(D_209,'#skF_2')
      | ~ m1_subset_1(D_209,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_34])).

tff(c_1104,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1100])).

tff(c_1178,plain,(
    ! [B_224] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_224))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_224),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_224),'#skF_2')
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1104])).

tff(c_1185,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1178])).

tff(c_1191,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1021,c_962,c_1185])).

tff(c_1725,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1720,c_1191])).

tff(c_1739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_955,c_1725])).

tff(c_1740,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2338,plain,(
    ! [B_358,A_359,C_360] :
      ( r2_hidden(B_358,k1_tops_1(A_359,C_360))
      | ~ m1_connsp_2(C_360,A_359,B_358)
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(A_359)))
      | ~ m1_subset_1(B_358,u1_struct_0(A_359))
      | ~ l1_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | v2_struct_0(A_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2344,plain,(
    ! [B_358] :
      ( r2_hidden(B_358,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_2338])).

tff(c_2352,plain,(
    ! [B_358] :
      ( r2_hidden(B_358,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_358)
      | ~ m1_subset_1(B_358,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2344])).

tff(c_2354,plain,(
    ! [B_361] :
      ( r2_hidden(B_361,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_361)
      | ~ m1_subset_1(B_361,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2352])).

tff(c_1786,plain,(
    ! [A_291,B_292] :
      ( v3_pre_topc(k1_tops_1(A_291,B_292),A_291)
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1788,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1786])).

tff(c_1791,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_1788])).

tff(c_1762,plain,(
    ! [A_284,B_285] :
      ( r1_tarski(k1_tops_1(A_284,B_285),B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1764,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1762])).

tff(c_1767,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1764])).

tff(c_1741,plain,(
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

tff(c_1800,plain,(
    ! [D_295] :
      ( ~ r2_hidden('#skF_3',D_295)
      | ~ r1_tarski(D_295,'#skF_4')
      | ~ v3_pre_topc(D_295,'#skF_2')
      | ~ m1_subset_1(D_295,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1741,c_42])).

tff(c_1804,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1800])).

tff(c_1968,plain,(
    ! [B_328] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_328))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_328),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_328),'#skF_2')
      | ~ m1_subset_1(B_328,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1804])).

tff(c_1975,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1968])).

tff(c_1981,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1791,c_1767,c_1975])).

tff(c_2359,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2354,c_1981])).

tff(c_2373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1740,c_2359])).

tff(c_2374,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2879,plain,(
    ! [B_436,A_437,C_438] :
      ( r2_hidden(B_436,k1_tops_1(A_437,C_438))
      | ~ m1_connsp_2(C_438,A_437,B_436)
      | ~ m1_subset_1(C_438,k1_zfmisc_1(u1_struct_0(A_437)))
      | ~ m1_subset_1(B_436,u1_struct_0(A_437))
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2885,plain,(
    ! [B_436] :
      ( r2_hidden(B_436,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_436)
      | ~ m1_subset_1(B_436,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_2879])).

tff(c_2893,plain,(
    ! [B_436] :
      ( r2_hidden(B_436,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_436)
      | ~ m1_subset_1(B_436,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2885])).

tff(c_2895,plain,(
    ! [B_439] :
      ( r2_hidden(B_439,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_439)
      | ~ m1_subset_1(B_439,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2893])).

tff(c_2405,plain,(
    ! [A_375,B_376] :
      ( v3_pre_topc(k1_tops_1(A_375,B_376),A_375)
      | ~ m1_subset_1(B_376,k1_zfmisc_1(u1_struct_0(A_375)))
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2407,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2405])).

tff(c_2410,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_2407])).

tff(c_2390,plain,(
    ! [A_370,B_371] :
      ( r1_tarski(k1_tops_1(A_370,B_371),B_371)
      | ~ m1_subset_1(B_371,k1_zfmisc_1(u1_struct_0(A_370)))
      | ~ l1_pre_topc(A_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2392,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2390])).

tff(c_2395,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2392])).

tff(c_2420,plain,(
    ! [A_378,B_379] :
      ( m1_subset_1(k1_tops_1(A_378,B_379),k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ l1_pre_topc(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2375,plain,(
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

tff(c_2411,plain,(
    ! [D_60] :
      ( ~ r2_hidden('#skF_3',D_60)
      | ~ r1_tarski(D_60,'#skF_4')
      | ~ v3_pre_topc(D_60,'#skF_2')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2375,c_38])).

tff(c_2424,plain,(
    ! [B_379] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_379))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_379),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_379),'#skF_2')
      | ~ m1_subset_1(B_379,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2420,c_2411])).

tff(c_2523,plain,(
    ! [B_403] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_403))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_403),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_403),'#skF_2')
      | ~ m1_subset_1(B_403,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2424])).

tff(c_2530,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2523])).

tff(c_2536,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2410,c_2395,c_2530])).

tff(c_2900,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2895,c_2536])).

tff(c_2914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2374,c_2900])).

tff(c_2915,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_4566,plain,(
    ! [B_670,A_671,C_672] :
      ( r2_hidden(B_670,k1_tops_1(A_671,C_672))
      | ~ m1_connsp_2(C_672,A_671,B_670)
      | ~ m1_subset_1(C_672,k1_zfmisc_1(u1_struct_0(A_671)))
      | ~ m1_subset_1(B_670,u1_struct_0(A_671))
      | ~ l1_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | v2_struct_0(A_671) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4570,plain,(
    ! [B_670] :
      ( r2_hidden(B_670,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_670)
      | ~ m1_subset_1(B_670,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_4566])).

tff(c_4574,plain,(
    ! [B_670] :
      ( r2_hidden(B_670,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_670)
      | ~ m1_subset_1(B_670,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_4570])).

tff(c_4576,plain,(
    ! [B_673] :
      ( r2_hidden(B_673,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_673)
      | ~ m1_subset_1(B_673,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_4574])).

tff(c_4011,plain,(
    ! [A_595,B_596] :
      ( v3_pre_topc(k1_tops_1(A_595,B_596),A_595)
      | ~ m1_subset_1(B_596,k1_zfmisc_1(u1_struct_0(A_595)))
      | ~ l1_pre_topc(A_595)
      | ~ v2_pre_topc(A_595) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4013,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_4011])).

tff(c_4016,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_4013])).

tff(c_2941,plain,(
    ! [A_451,B_452] :
      ( r1_tarski(k1_tops_1(A_451,B_452),B_452)
      | ~ m1_subset_1(B_452,k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ l1_pre_topc(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2943,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_2941])).

tff(c_2946,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2943])).

tff(c_4032,plain,(
    ! [A_599,B_600] :
      ( m1_subset_1(k1_tops_1(A_599,B_600),k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ l1_pre_topc(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2916,plain,(
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

tff(c_3983,plain,(
    ! [D_60] :
      ( ~ r2_hidden('#skF_3',D_60)
      | ~ r1_tarski(D_60,'#skF_4')
      | ~ v3_pre_topc(D_60,'#skF_2')
      | ~ m1_subset_1(D_60,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2916,c_46])).

tff(c_4038,plain,(
    ! [B_600] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_600))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_600),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_600),'#skF_2')
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4032,c_3983])).

tff(c_4102,plain,(
    ! [B_616] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_616))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_616),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_616),'#skF_2')
      | ~ m1_subset_1(B_616,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_4038])).

tff(c_4109,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_4102])).

tff(c_4115,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4016,c_2946,c_4109])).

tff(c_4579,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4576,c_4115])).

tff(c_4589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2915,c_4579])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:36:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.96/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.96/2.14  
% 5.96/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.14  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.02/2.14  
% 6.02/2.14  %Foreground sorts:
% 6.02/2.14  
% 6.02/2.14  
% 6.02/2.14  %Background operators:
% 6.02/2.14  
% 6.02/2.14  
% 6.02/2.14  %Foreground operators:
% 6.02/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.02/2.14  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.02/2.14  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.02/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.02/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.02/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.02/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.02/2.14  tff('#skF_5', type, '#skF_5': $i).
% 6.02/2.14  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.02/2.14  tff('#skF_2', type, '#skF_2': $i).
% 6.02/2.14  tff('#skF_3', type, '#skF_3': $i).
% 6.02/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.02/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.02/2.14  tff('#skF_4', type, '#skF_4': $i).
% 6.02/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.02/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.02/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.02/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.02/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.02/2.14  
% 6.02/2.17  tff(f_128, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_connsp_2)).
% 6.02/2.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.02/2.17  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 6.02/2.17  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_tops_1)).
% 6.02/2.17  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 6.02/2.17  tff(f_46, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.02/2.17  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 6.02/2.17  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.02/2.17  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_48, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_53, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 6.02/2.17  tff(c_44, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_55, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 6.02/2.17  tff(c_40, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_54, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_40])).
% 6.02/2.17  tff(c_52, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_71, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_52])).
% 6.02/2.17  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_34, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_217, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 6.02/2.17  tff(c_30, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_28, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.17  tff(c_57, plain, (![A_63, B_64]: (~r2_hidden('#skF_1'(A_63, B_64), B_64) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.17  tff(c_62, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_57])).
% 6.02/2.17  tff(c_18, plain, (![B_28, D_34, C_32, A_20]: (k1_tops_1(B_28, D_34)=D_34 | ~v3_pre_topc(D_34, B_28) | ~m1_subset_1(D_34, k1_zfmisc_1(u1_struct_0(B_28))) | ~m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(B_28) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.02/2.17  tff(c_567, plain, (![C_140, A_141]: (~m1_subset_1(C_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141))), inference(splitLeft, [status(thm)], [c_18])).
% 6.02/2.17  tff(c_573, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_71, c_567])).
% 6.02/2.17  tff(c_581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_573])).
% 6.02/2.17  tff(c_588, plain, (![B_144, D_145]: (k1_tops_1(B_144, D_145)=D_145 | ~v3_pre_topc(D_145, B_144) | ~m1_subset_1(D_145, k1_zfmisc_1(u1_struct_0(B_144))) | ~l1_pre_topc(B_144))), inference(splitRight, [status(thm)], [c_18])).
% 6.02/2.17  tff(c_594, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5' | ~v3_pre_topc('#skF_5', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_71, c_588])).
% 6.02/2.17  tff(c_601, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_53, c_594])).
% 6.02/2.17  tff(c_14, plain, (![A_13, B_17, C_19]: (r1_tarski(k1_tops_1(A_13, B_17), k1_tops_1(A_13, C_19)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.02/2.17  tff(c_630, plain, (![C_19]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_19)) | ~r1_tarski('#skF_5', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_601, c_14])).
% 6.02/2.17  tff(c_669, plain, (![C_148]: (r1_tarski('#skF_5', k1_tops_1('#skF_2', C_148)) | ~r1_tarski('#skF_5', C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_71, c_630])).
% 6.02/2.17  tff(c_679, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_669])).
% 6.02/2.17  tff(c_688, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_679])).
% 6.02/2.17  tff(c_64, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.17  tff(c_72, plain, (![B_69]: (r2_hidden('#skF_3', B_69) | ~r1_tarski('#skF_5', B_69))), inference(resolution, [status(thm)], [c_54, c_64])).
% 6.02/2.17  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.02/2.17  tff(c_75, plain, (![B_2, B_69]: (r2_hidden('#skF_3', B_2) | ~r1_tarski(B_69, B_2) | ~r1_tarski('#skF_5', B_69))), inference(resolution, [status(thm)], [c_72, c_2])).
% 6.02/2.17  tff(c_699, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_688, c_75])).
% 6.02/2.17  tff(c_707, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_699])).
% 6.02/2.17  tff(c_858, plain, (![C_165, A_166, B_167]: (m1_connsp_2(C_165, A_166, B_167) | ~r2_hidden(B_167, k1_tops_1(A_166, C_165)) | ~m1_subset_1(C_165, k1_zfmisc_1(u1_struct_0(A_166))) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.02/2.17  tff(c_867, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_707, c_858])).
% 6.02/2.17  tff(c_899, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_867])).
% 6.02/2.17  tff(c_901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_217, c_899])).
% 6.02/2.17  tff(c_937, plain, (![D_174]: (~r2_hidden('#skF_3', D_174) | ~r1_tarski(D_174, '#skF_4') | ~v3_pre_topc(D_174, '#skF_2') | ~m1_subset_1(D_174, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_34])).
% 6.02/2.17  tff(c_944, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_71, c_937])).
% 6.02/2.17  tff(c_954, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_55, c_54, c_944])).
% 6.02/2.17  tff(c_955, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 6.02/2.17  tff(c_1704, plain, (![B_271, A_272, C_273]: (r2_hidden(B_271, k1_tops_1(A_272, C_273)) | ~m1_connsp_2(C_273, A_272, B_271) | ~m1_subset_1(C_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~m1_subset_1(B_271, u1_struct_0(A_272)) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.02/2.17  tff(c_1710, plain, (![B_271]: (r2_hidden(B_271, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_271) | ~m1_subset_1(B_271, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1704])).
% 6.02/2.17  tff(c_1718, plain, (![B_271]: (r2_hidden(B_271, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_271) | ~m1_subset_1(B_271, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1710])).
% 6.02/2.17  tff(c_1720, plain, (![B_274]: (r2_hidden(B_274, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_274) | ~m1_subset_1(B_274, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_1718])).
% 6.02/2.17  tff(c_1013, plain, (![A_188, B_189]: (v3_pre_topc(k1_tops_1(A_188, B_189), A_188) | ~m1_subset_1(B_189, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188) | ~v2_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.17  tff(c_1017, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1013])).
% 6.02/2.17  tff(c_1021, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1017])).
% 6.02/2.17  tff(c_957, plain, (![A_175, B_176]: (r1_tarski(k1_tops_1(A_175, B_176), B_176) | ~m1_subset_1(B_176, k1_zfmisc_1(u1_struct_0(A_175))) | ~l1_pre_topc(A_175))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.17  tff(c_959, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_957])).
% 6.02/2.17  tff(c_962, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_959])).
% 6.02/2.17  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.02/2.17  tff(c_1100, plain, (![D_209]: (~r2_hidden('#skF_3', D_209) | ~r1_tarski(D_209, '#skF_4') | ~v3_pre_topc(D_209, '#skF_2') | ~m1_subset_1(D_209, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_955, c_34])).
% 6.02/2.17  tff(c_1104, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1100])).
% 6.02/2.17  tff(c_1178, plain, (![B_224]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_224)) | ~r1_tarski(k1_tops_1('#skF_2', B_224), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_224), '#skF_2') | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1104])).
% 6.02/2.17  tff(c_1185, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_1178])).
% 6.02/2.17  tff(c_1191, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1021, c_962, c_1185])).
% 6.02/2.17  tff(c_1725, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1720, c_1191])).
% 6.02/2.17  tff(c_1739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_955, c_1725])).
% 6.02/2.17  tff(c_1740, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_44])).
% 6.02/2.17  tff(c_2338, plain, (![B_358, A_359, C_360]: (r2_hidden(B_358, k1_tops_1(A_359, C_360)) | ~m1_connsp_2(C_360, A_359, B_358) | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(A_359))) | ~m1_subset_1(B_358, u1_struct_0(A_359)) | ~l1_pre_topc(A_359) | ~v2_pre_topc(A_359) | v2_struct_0(A_359))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.02/2.17  tff(c_2344, plain, (![B_358]: (r2_hidden(B_358, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2338])).
% 6.02/2.17  tff(c_2352, plain, (![B_358]: (r2_hidden(B_358, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_358) | ~m1_subset_1(B_358, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2344])).
% 6.02/2.17  tff(c_2354, plain, (![B_361]: (r2_hidden(B_361, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_361) | ~m1_subset_1(B_361, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2352])).
% 6.02/2.17  tff(c_1786, plain, (![A_291, B_292]: (v3_pre_topc(k1_tops_1(A_291, B_292), A_291) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.17  tff(c_1788, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1786])).
% 6.02/2.17  tff(c_1791, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_1788])).
% 6.02/2.17  tff(c_1762, plain, (![A_284, B_285]: (r1_tarski(k1_tops_1(A_284, B_285), B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.17  tff(c_1764, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1762])).
% 6.02/2.17  tff(c_1767, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1764])).
% 6.02/2.17  tff(c_1741, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 6.02/2.17  tff(c_42, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_1800, plain, (![D_295]: (~r2_hidden('#skF_3', D_295) | ~r1_tarski(D_295, '#skF_4') | ~v3_pre_topc(D_295, '#skF_2') | ~m1_subset_1(D_295, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1741, c_42])).
% 6.02/2.17  tff(c_1804, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1800])).
% 6.02/2.17  tff(c_1968, plain, (![B_328]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_328)) | ~r1_tarski(k1_tops_1('#skF_2', B_328), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_328), '#skF_2') | ~m1_subset_1(B_328, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1804])).
% 6.02/2.17  tff(c_1975, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_1968])).
% 6.02/2.17  tff(c_1981, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1791, c_1767, c_1975])).
% 6.02/2.17  tff(c_2359, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2354, c_1981])).
% 6.02/2.17  tff(c_2373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1740, c_2359])).
% 6.02/2.17  tff(c_2374, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_40])).
% 6.02/2.17  tff(c_2879, plain, (![B_436, A_437, C_438]: (r2_hidden(B_436, k1_tops_1(A_437, C_438)) | ~m1_connsp_2(C_438, A_437, B_436) | ~m1_subset_1(C_438, k1_zfmisc_1(u1_struct_0(A_437))) | ~m1_subset_1(B_436, u1_struct_0(A_437)) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.02/2.17  tff(c_2885, plain, (![B_436]: (r2_hidden(B_436, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_436) | ~m1_subset_1(B_436, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_2879])).
% 6.02/2.17  tff(c_2893, plain, (![B_436]: (r2_hidden(B_436, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_436) | ~m1_subset_1(B_436, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2885])).
% 6.02/2.17  tff(c_2895, plain, (![B_439]: (r2_hidden(B_439, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_439) | ~m1_subset_1(B_439, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_2893])).
% 6.02/2.17  tff(c_2405, plain, (![A_375, B_376]: (v3_pre_topc(k1_tops_1(A_375, B_376), A_375) | ~m1_subset_1(B_376, k1_zfmisc_1(u1_struct_0(A_375))) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.17  tff(c_2407, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2405])).
% 6.02/2.17  tff(c_2410, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_2407])).
% 6.02/2.17  tff(c_2390, plain, (![A_370, B_371]: (r1_tarski(k1_tops_1(A_370, B_371), B_371) | ~m1_subset_1(B_371, k1_zfmisc_1(u1_struct_0(A_370))) | ~l1_pre_topc(A_370))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.17  tff(c_2392, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2390])).
% 6.02/2.17  tff(c_2395, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2392])).
% 6.02/2.17  tff(c_2420, plain, (![A_378, B_379]: (m1_subset_1(k1_tops_1(A_378, B_379), k1_zfmisc_1(u1_struct_0(A_378))) | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0(A_378))) | ~l1_pre_topc(A_378))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.02/2.17  tff(c_2375, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 6.02/2.17  tff(c_38, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_2411, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2375, c_38])).
% 6.02/2.17  tff(c_2424, plain, (![B_379]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_379)) | ~r1_tarski(k1_tops_1('#skF_2', B_379), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_379), '#skF_2') | ~m1_subset_1(B_379, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2420, c_2411])).
% 6.02/2.17  tff(c_2523, plain, (![B_403]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_403)) | ~r1_tarski(k1_tops_1('#skF_2', B_403), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_403), '#skF_2') | ~m1_subset_1(B_403, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2424])).
% 6.02/2.17  tff(c_2530, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_2523])).
% 6.02/2.17  tff(c_2536, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2410, c_2395, c_2530])).
% 6.02/2.17  tff(c_2900, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2895, c_2536])).
% 6.02/2.17  tff(c_2914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2374, c_2900])).
% 6.02/2.17  tff(c_2915, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_48])).
% 6.02/2.17  tff(c_4566, plain, (![B_670, A_671, C_672]: (r2_hidden(B_670, k1_tops_1(A_671, C_672)) | ~m1_connsp_2(C_672, A_671, B_670) | ~m1_subset_1(C_672, k1_zfmisc_1(u1_struct_0(A_671))) | ~m1_subset_1(B_670, u1_struct_0(A_671)) | ~l1_pre_topc(A_671) | ~v2_pre_topc(A_671) | v2_struct_0(A_671))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.02/2.17  tff(c_4570, plain, (![B_670]: (r2_hidden(B_670, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_670) | ~m1_subset_1(B_670, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_4566])).
% 6.02/2.17  tff(c_4574, plain, (![B_670]: (r2_hidden(B_670, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_670) | ~m1_subset_1(B_670, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_4570])).
% 6.02/2.17  tff(c_4576, plain, (![B_673]: (r2_hidden(B_673, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_673) | ~m1_subset_1(B_673, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_32, c_4574])).
% 6.02/2.17  tff(c_4011, plain, (![A_595, B_596]: (v3_pre_topc(k1_tops_1(A_595, B_596), A_595) | ~m1_subset_1(B_596, k1_zfmisc_1(u1_struct_0(A_595))) | ~l1_pre_topc(A_595) | ~v2_pre_topc(A_595))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.02/2.17  tff(c_4013, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_4011])).
% 6.02/2.17  tff(c_4016, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_4013])).
% 6.02/2.17  tff(c_2941, plain, (![A_451, B_452]: (r1_tarski(k1_tops_1(A_451, B_452), B_452) | ~m1_subset_1(B_452, k1_zfmisc_1(u1_struct_0(A_451))) | ~l1_pre_topc(A_451))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.02/2.17  tff(c_2943, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_24, c_2941])).
% 6.02/2.17  tff(c_2946, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_2943])).
% 6.02/2.17  tff(c_4032, plain, (![A_599, B_600]: (m1_subset_1(k1_tops_1(A_599, B_600), k1_zfmisc_1(u1_struct_0(A_599))) | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0(A_599))) | ~l1_pre_topc(A_599))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.02/2.17  tff(c_2916, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.02/2.17  tff(c_46, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.02/2.17  tff(c_3983, plain, (![D_60]: (~r2_hidden('#skF_3', D_60) | ~r1_tarski(D_60, '#skF_4') | ~v3_pre_topc(D_60, '#skF_2') | ~m1_subset_1(D_60, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2916, c_46])).
% 6.02/2.17  tff(c_4038, plain, (![B_600]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_600)) | ~r1_tarski(k1_tops_1('#skF_2', B_600), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_600), '#skF_2') | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_4032, c_3983])).
% 6.02/2.17  tff(c_4102, plain, (![B_616]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_616)) | ~r1_tarski(k1_tops_1('#skF_2', B_616), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_616), '#skF_2') | ~m1_subset_1(B_616, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_4038])).
% 6.02/2.17  tff(c_4109, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_4102])).
% 6.02/2.17  tff(c_4115, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4016, c_2946, c_4109])).
% 6.02/2.17  tff(c_4579, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4576, c_4115])).
% 6.02/2.17  tff(c_4589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2915, c_4579])).
% 6.02/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.02/2.17  
% 6.02/2.17  Inference rules
% 6.02/2.17  ----------------------
% 6.02/2.17  #Ref     : 0
% 6.02/2.17  #Sup     : 932
% 6.02/2.17  #Fact    : 0
% 6.02/2.17  #Define  : 0
% 6.02/2.17  #Split   : 38
% 6.02/2.17  #Chain   : 0
% 6.02/2.17  #Close   : 0
% 6.02/2.17  
% 6.02/2.17  Ordering : KBO
% 6.02/2.17  
% 6.02/2.17  Simplification rules
% 6.02/2.17  ----------------------
% 6.02/2.17  #Subsume      : 343
% 6.02/2.17  #Demod        : 859
% 6.02/2.17  #Tautology    : 219
% 6.02/2.17  #SimpNegUnit  : 53
% 6.02/2.17  #BackRed      : 57
% 6.02/2.17  
% 6.02/2.17  #Partial instantiations: 0
% 6.02/2.17  #Strategies tried      : 1
% 6.02/2.17  
% 6.02/2.17  Timing (in seconds)
% 6.02/2.17  ----------------------
% 6.02/2.18  Preprocessing        : 0.32
% 6.02/2.18  Parsing              : 0.18
% 6.02/2.18  CNF conversion       : 0.02
% 6.02/2.18  Main loop            : 1.03
% 6.02/2.18  Inferencing          : 0.37
% 6.02/2.18  Reduction            : 0.31
% 6.02/2.18  Demodulation         : 0.21
% 6.02/2.18  BG Simplification    : 0.04
% 6.02/2.18  Subsumption          : 0.25
% 6.02/2.18  Abstraction          : 0.04
% 6.02/2.18  MUC search           : 0.00
% 6.02/2.18  Cooper               : 0.00
% 6.02/2.18  Total                : 1.41
% 6.02/2.18  Index Insertion      : 0.00
% 6.02/2.18  Index Deletion       : 0.00
% 6.02/2.18  Index Matching       : 0.00
% 6.02/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
