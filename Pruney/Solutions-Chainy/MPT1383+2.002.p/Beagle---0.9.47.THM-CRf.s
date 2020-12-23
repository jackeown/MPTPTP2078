%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:11 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 472 expanded)
%              Number of leaves         :   27 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  445 (2105 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_126,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_51,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_53,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_50,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_69,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_32,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_215,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_28,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_26,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_119,plain,(
    ! [A_72,B_73] :
      ( v3_pre_topc(k1_tops_1(A_72,B_73),A_72)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_123,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_119])).

tff(c_129,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_123])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tops_1(A_6,B_7),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_742,plain,(
    ! [B_153,A_154,C_155] :
      ( m1_connsp_2(B_153,A_154,C_155)
      | ~ r2_hidden(C_155,B_153)
      | ~ v3_pre_topc(B_153,A_154)
      | ~ m1_subset_1(C_155,u1_struct_0(A_154))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_744,plain,(
    ! [B_153] :
      ( m1_connsp_2(B_153,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_153)
      | ~ v3_pre_topc(B_153,'#skF_2')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_742])).

tff(c_747,plain,(
    ! [B_153] :
      ( m1_connsp_2(B_153,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_153)
      | ~ v3_pre_topc(B_153,'#skF_2')
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_744])).

tff(c_749,plain,(
    ! [B_156] :
      ( m1_connsp_2(B_156,'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',B_156)
      | ~ v3_pre_topc(B_156,'#skF_2')
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_747])).

tff(c_753,plain,(
    ! [B_7] :
      ( m1_connsp_2(k1_tops_1('#skF_2',B_7),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_749])).

tff(c_883,plain,(
    ! [B_174] :
      ( m1_connsp_2(k1_tops_1('#skF_2',B_174),'#skF_2','#skF_3')
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_174))
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_174),'#skF_2')
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_753])).

tff(c_893,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_883])).

tff(c_902,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_893])).

tff(c_903,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_902])).

tff(c_14,plain,(
    ! [A_13,B_17,C_19] :
      ( r1_tarski(k1_tops_1(A_13,B_17),k1_tops_1(A_13,C_19))
      | ~ r1_tarski(B_17,C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_756,plain,
    ( m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_749])).

tff(c_765,plain,(
    m1_connsp_2('#skF_5','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_52,c_756])).

tff(c_487,plain,(
    ! [B_118,A_119,C_120] :
      ( r2_hidden(B_118,k1_tops_1(A_119,C_120))
      | ~ m1_connsp_2(C_120,A_119,B_118)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_118,u1_struct_0(A_119))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_491,plain,(
    ! [B_118] :
      ( r2_hidden(B_118,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_118)
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_69,c_487])).

tff(c_497,plain,(
    ! [B_118] :
      ( r2_hidden(B_118,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_118)
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_491])).

tff(c_498,plain,(
    ! [B_118] :
      ( r2_hidden(B_118,k1_tops_1('#skF_2','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_2',B_118)
      | ~ m1_subset_1(B_118,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_497])).

tff(c_121,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_119])).

tff(c_126,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_121])).

tff(c_890,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_5'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5'))
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_883])).

tff(c_899,plain,
    ( m1_connsp_2(k1_tops_1('#skF_2','#skF_5'),'#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_890])).

tff(c_918,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_899])).

tff(c_922,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_498,c_918])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_765,c_922])).

tff(c_934,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_899])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_963,plain,(
    ! [B_180] :
      ( r2_hidden('#skF_3',B_180)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_5'),B_180) ) ),
    inference(resolution,[status(thm)],[c_934,c_2])).

tff(c_967,plain,(
    ! [C_19] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_19))
      | ~ r1_tarski('#skF_5',C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_963])).

tff(c_987,plain,(
    ! [C_181] :
      ( r2_hidden('#skF_3',k1_tops_1('#skF_2',C_181))
      | ~ r1_tarski('#skF_5',C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_69,c_967])).

tff(c_997,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_987])).

tff(c_1006,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_997])).

tff(c_1008,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_903,c_1006])).

tff(c_1010,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_902])).

tff(c_16,plain,(
    ! [C_26,A_20,B_24] :
      ( m1_connsp_2(C_26,A_20,B_24)
      | ~ r2_hidden(B_24,k1_tops_1(A_20,C_26))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,u1_struct_0(A_20))
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1012,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1010,c_16])).

tff(c_1017,plain,
    ( m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_1012])).

tff(c_1019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_215,c_1017])).

tff(c_1031,plain,(
    ! [D_184] :
      ( ~ r2_hidden('#skF_3',D_184)
      | ~ r1_tarski(D_184,'#skF_4')
      | ~ v3_pre_topc(D_184,'#skF_2')
      | ~ m1_subset_1(D_184,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_1038,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_1031])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_53,c_52,c_1038])).

tff(c_1049,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1514,plain,(
    ! [B_262,A_263,C_264] :
      ( r2_hidden(B_262,k1_tops_1(A_263,C_264))
      | ~ m1_connsp_2(C_264,A_263,B_262)
      | ~ m1_subset_1(C_264,k1_zfmisc_1(u1_struct_0(A_263)))
      | ~ m1_subset_1(B_262,u1_struct_0(A_263))
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1518,plain,(
    ! [B_262] :
      ( r2_hidden(B_262,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_262)
      | ~ m1_subset_1(B_262,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_1514])).

tff(c_1522,plain,(
    ! [B_262] :
      ( r2_hidden(B_262,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_262)
      | ~ m1_subset_1(B_262,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1518])).

tff(c_1524,plain,(
    ! [B_265] :
      ( r2_hidden(B_265,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_265)
      | ~ m1_subset_1(B_265,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1522])).

tff(c_1107,plain,(
    ! [A_198,B_199] :
      ( v3_pre_topc(k1_tops_1(A_198,B_199),A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1111,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1107])).

tff(c_1115,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1111])).

tff(c_1089,plain,(
    ! [A_194,B_195] :
      ( r1_tarski(k1_tops_1(A_194,B_195),B_195)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1091,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1089])).

tff(c_1094,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1091])).

tff(c_1176,plain,(
    ! [D_215] :
      ( ~ r2_hidden('#skF_3',D_215)
      | ~ r1_tarski(D_215,'#skF_4')
      | ~ v3_pre_topc(D_215,'#skF_2')
      | ~ m1_subset_1(D_215,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_32])).

tff(c_1180,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1176])).

tff(c_1255,plain,(
    ! [B_228] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_228))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_228),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_228),'#skF_2')
      | ~ m1_subset_1(B_228,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1180])).

tff(c_1262,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1255])).

tff(c_1268,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1115,c_1094,c_1262])).

tff(c_1529,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1524,c_1268])).

tff(c_1543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1049,c_1529])).

tff(c_1544,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2001,plain,(
    ! [B_340,A_341,C_342] :
      ( r2_hidden(B_340,k1_tops_1(A_341,C_342))
      | ~ m1_connsp_2(C_342,A_341,B_340)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(u1_struct_0(A_341)))
      | ~ m1_subset_1(B_340,u1_struct_0(A_341))
      | ~ l1_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | v2_struct_0(A_341) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2007,plain,(
    ! [B_340] :
      ( r2_hidden(B_340,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_340)
      | ~ m1_subset_1(B_340,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_2001])).

tff(c_2015,plain,(
    ! [B_340] :
      ( r2_hidden(B_340,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_340)
      | ~ m1_subset_1(B_340,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2007])).

tff(c_2017,plain,(
    ! [B_343] :
      ( r2_hidden(B_343,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_343)
      | ~ m1_subset_1(B_343,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2015])).

tff(c_1599,plain,(
    ! [A_282,B_283] :
      ( v3_pre_topc(k1_tops_1(A_282,B_283),A_282)
      | ~ m1_subset_1(B_283,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1603,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1599])).

tff(c_1609,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_1603])).

tff(c_1580,plain,(
    ! [A_280,B_281] :
      ( r1_tarski(k1_tops_1(A_280,B_281),B_281)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(u1_struct_0(A_280)))
      | ~ l1_pre_topc(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1584,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1580])).

tff(c_1590,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1584])).

tff(c_1545,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_40,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1654,plain,(
    ! [D_295] :
      ( ~ r2_hidden('#skF_3',D_295)
      | ~ r1_tarski(D_295,'#skF_4')
      | ~ v3_pre_topc(D_295,'#skF_2')
      | ~ m1_subset_1(D_295,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1545,c_40])).

tff(c_1658,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_7))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_7),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_7),'#skF_2')
      | ~ m1_subset_1(B_7,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_1654])).

tff(c_1743,plain,(
    ! [B_305] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_305))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_305),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_305),'#skF_2')
      | ~ m1_subset_1(B_305,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1658])).

tff(c_1753,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1743])).

tff(c_1762,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1609,c_1590,c_1753])).

tff(c_2022,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2017,c_1762])).

tff(c_2036,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1544,c_2022])).

tff(c_2037,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2267,plain,(
    ! [B_395,A_396,C_397] :
      ( r2_hidden(B_395,k1_tops_1(A_396,C_397))
      | ~ m1_connsp_2(C_397,A_396,B_395)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(u1_struct_0(A_396)))
      | ~ m1_subset_1(B_395,u1_struct_0(A_396))
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2271,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_2267])).

tff(c_2275,plain,(
    ! [B_395] :
      ( r2_hidden(B_395,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_395)
      | ~ m1_subset_1(B_395,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2271])).

tff(c_2277,plain,(
    ! [B_398] :
      ( r2_hidden(B_398,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_398)
      | ~ m1_subset_1(B_398,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_2275])).

tff(c_2068,plain,(
    ! [A_357,B_358] :
      ( v3_pre_topc(k1_tops_1(A_357,B_358),A_357)
      | ~ m1_subset_1(B_358,k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2070,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2068])).

tff(c_2073,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2070])).

tff(c_2053,plain,(
    ! [A_352,B_353] :
      ( r1_tarski(k1_tops_1(A_352,B_353),B_353)
      | ~ m1_subset_1(B_353,k1_zfmisc_1(u1_struct_0(A_352)))
      | ~ l1_pre_topc(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2055,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2053])).

tff(c_2058,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2055])).

tff(c_2083,plain,(
    ! [A_360,B_361] :
      ( m1_subset_1(k1_tops_1(A_360,B_361),k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0(A_360)))
      | ~ l1_pre_topc(A_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2038,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2074,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2038,c_36])).

tff(c_2087,plain,(
    ! [B_361] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_361))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_361),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_361),'#skF_2')
      | ~ m1_subset_1(B_361,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2083,c_2074])).

tff(c_2186,plain,(
    ! [B_385] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_385))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_385),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_385),'#skF_2')
      | ~ m1_subset_1(B_385,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2087])).

tff(c_2193,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2186])).

tff(c_2199,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2073,c_2058,c_2193])).

tff(c_2280,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2277,c_2199])).

tff(c_2290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2037,c_2280])).

tff(c_2291,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3259,plain,(
    ! [B_573,A_574,C_575] :
      ( r2_hidden(B_573,k1_tops_1(A_574,C_575))
      | ~ m1_connsp_2(C_575,A_574,B_573)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(u1_struct_0(A_574)))
      | ~ m1_subset_1(B_573,u1_struct_0(A_574))
      | ~ l1_pre_topc(A_574)
      | ~ v2_pre_topc(A_574)
      | v2_struct_0(A_574) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3263,plain,(
    ! [B_573] :
      ( r2_hidden(B_573,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_573)
      | ~ m1_subset_1(B_573,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_3259])).

tff(c_3267,plain,(
    ! [B_573] :
      ( r2_hidden(B_573,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_573)
      | ~ m1_subset_1(B_573,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_3263])).

tff(c_3269,plain,(
    ! [B_576] :
      ( r2_hidden(B_576,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_576)
      | ~ m1_subset_1(B_576,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_3267])).

tff(c_2959,plain,(
    ! [A_521,B_522] :
      ( v3_pre_topc(k1_tops_1(A_521,B_522),A_521)
      | ~ m1_subset_1(B_522,k1_zfmisc_1(u1_struct_0(A_521)))
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2961,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2959])).

tff(c_2964,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_2961])).

tff(c_2317,plain,(
    ! [A_410,B_411] :
      ( r1_tarski(k1_tops_1(A_410,B_411),B_411)
      | ~ m1_subset_1(B_411,k1_zfmisc_1(u1_struct_0(A_410)))
      | ~ l1_pre_topc(A_410) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2319,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_2317])).

tff(c_2322,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2319])).

tff(c_2965,plain,(
    ! [A_523,B_524] :
      ( m1_subset_1(k1_tops_1(A_523,B_524),k1_zfmisc_1(u1_struct_0(A_523)))
      | ~ m1_subset_1(B_524,k1_zfmisc_1(u1_struct_0(A_523)))
      | ~ l1_pre_topc(A_523) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2292,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_44,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_2935,plain,(
    ! [D_52] :
      ( ~ r2_hidden('#skF_3',D_52)
      | ~ r1_tarski(D_52,'#skF_4')
      | ~ v3_pre_topc(D_52,'#skF_2')
      | ~ m1_subset_1(D_52,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2292,c_44])).

tff(c_2971,plain,(
    ! [B_524] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_524))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_524),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_524),'#skF_2')
      | ~ m1_subset_1(B_524,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2965,c_2935])).

tff(c_3076,plain,(
    ! [B_544] :
      ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2',B_544))
      | ~ r1_tarski(k1_tops_1('#skF_2',B_544),'#skF_4')
      | ~ v3_pre_topc(k1_tops_1('#skF_2',B_544),'#skF_2')
      | ~ m1_subset_1(B_544,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2971])).

tff(c_3083,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_3076])).

tff(c_3089,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2964,c_2322,c_3083])).

tff(c_3272,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_3269,c_3089])).

tff(c_3282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2291,c_3272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.21  
% 6.10/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.22  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.10/2.22  
% 6.10/2.22  %Foreground sorts:
% 6.10/2.22  
% 6.10/2.22  
% 6.10/2.22  %Background operators:
% 6.10/2.22  
% 6.10/2.22  
% 6.10/2.22  %Foreground operators:
% 6.10/2.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.10/2.22  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.10/2.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.10/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.10/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.22  tff('#skF_5', type, '#skF_5': $i).
% 6.10/2.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.10/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.10/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.10/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.22  tff('#skF_4', type, '#skF_4': $i).
% 6.10/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.10/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.10/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.10/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.22  
% 6.10/2.25  tff(f_126, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 6.10/2.25  tff(f_46, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 6.10/2.25  tff(f_38, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tops_1)).
% 6.10/2.25  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 6.10/2.25  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 6.10/2.25  tff(f_82, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 6.10/2.25  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.10/2.25  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 6.10/2.25  tff(c_24, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_46, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_51, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 6.10/2.25  tff(c_42, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_53, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_42])).
% 6.10/2.25  tff(c_38, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_52, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 6.10/2.25  tff(c_50, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_69, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_50])).
% 6.10/2.25  tff(c_30, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_32, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_connsp_2('#skF_4', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_215, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 6.10/2.25  tff(c_28, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_26, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_119, plain, (![A_72, B_73]: (v3_pre_topc(k1_tops_1(A_72, B_73), A_72) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.10/2.25  tff(c_123, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_119])).
% 6.10/2.25  tff(c_129, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_123])).
% 6.10/2.25  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tops_1(A_6, B_7), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0(A_6))) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.25  tff(c_742, plain, (![B_153, A_154, C_155]: (m1_connsp_2(B_153, A_154, C_155) | ~r2_hidden(C_155, B_153) | ~v3_pre_topc(B_153, A_154) | ~m1_subset_1(C_155, u1_struct_0(A_154)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.10/2.25  tff(c_744, plain, (![B_153]: (m1_connsp_2(B_153, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_153) | ~v3_pre_topc(B_153, '#skF_2') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_742])).
% 6.10/2.25  tff(c_747, plain, (![B_153]: (m1_connsp_2(B_153, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_153) | ~v3_pre_topc(B_153, '#skF_2') | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_744])).
% 6.10/2.25  tff(c_749, plain, (![B_156]: (m1_connsp_2(B_156, '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', B_156) | ~v3_pre_topc(B_156, '#skF_2') | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_30, c_747])).
% 6.10/2.25  tff(c_753, plain, (![B_7]: (m1_connsp_2(k1_tops_1('#skF_2', B_7), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_749])).
% 6.10/2.25  tff(c_883, plain, (![B_174]: (m1_connsp_2(k1_tops_1('#skF_2', B_174), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_174)) | ~v3_pre_topc(k1_tops_1('#skF_2', B_174), '#skF_2') | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_753])).
% 6.10/2.25  tff(c_893, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_883])).
% 6.10/2.25  tff(c_902, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_893])).
% 6.10/2.25  tff(c_903, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_902])).
% 6.10/2.25  tff(c_14, plain, (![A_13, B_17, C_19]: (r1_tarski(k1_tops_1(A_13, B_17), k1_tops_1(A_13, C_19)) | ~r1_tarski(B_17, C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.10/2.25  tff(c_756, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_69, c_749])).
% 6.10/2.25  tff(c_765, plain, (m1_connsp_2('#skF_5', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_52, c_756])).
% 6.10/2.25  tff(c_487, plain, (![B_118, A_119, C_120]: (r2_hidden(B_118, k1_tops_1(A_119, C_120)) | ~m1_connsp_2(C_120, A_119, B_118) | ~m1_subset_1(C_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_118, u1_struct_0(A_119)) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.25  tff(c_491, plain, (![B_118]: (r2_hidden(B_118, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_118) | ~m1_subset_1(B_118, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_69, c_487])).
% 6.10/2.25  tff(c_497, plain, (![B_118]: (r2_hidden(B_118, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_118) | ~m1_subset_1(B_118, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_491])).
% 6.10/2.25  tff(c_498, plain, (![B_118]: (r2_hidden(B_118, k1_tops_1('#skF_2', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_2', B_118) | ~m1_subset_1(B_118, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_497])).
% 6.10/2.25  tff(c_121, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_69, c_119])).
% 6.10/2.25  tff(c_126, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_121])).
% 6.10/2.25  tff(c_890, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_5'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5')) | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_69, c_883])).
% 6.10/2.25  tff(c_899, plain, (m1_connsp_2(k1_tops_1('#skF_2', '#skF_5'), '#skF_2', '#skF_3') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_890])).
% 6.10/2.25  tff(c_918, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(splitLeft, [status(thm)], [c_899])).
% 6.10/2.25  tff(c_922, plain, (~m1_connsp_2('#skF_5', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_498, c_918])).
% 6.10/2.25  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_765, c_922])).
% 6.10/2.25  tff(c_934, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_5'))), inference(splitRight, [status(thm)], [c_899])).
% 6.10/2.25  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.10/2.25  tff(c_963, plain, (![B_180]: (r2_hidden('#skF_3', B_180) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_5'), B_180))), inference(resolution, [status(thm)], [c_934, c_2])).
% 6.10/2.25  tff(c_967, plain, (![C_19]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_19)) | ~r1_tarski('#skF_5', C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_963])).
% 6.10/2.25  tff(c_987, plain, (![C_181]: (r2_hidden('#skF_3', k1_tops_1('#skF_2', C_181)) | ~r1_tarski('#skF_5', C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_69, c_967])).
% 6.10/2.25  tff(c_997, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_987])).
% 6.10/2.25  tff(c_1006, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_997])).
% 6.10/2.25  tff(c_1008, plain, $false, inference(negUnitSimplification, [status(thm)], [c_903, c_1006])).
% 6.10/2.25  tff(c_1010, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_902])).
% 6.10/2.25  tff(c_16, plain, (![C_26, A_20, B_24]: (m1_connsp_2(C_26, A_20, B_24) | ~r2_hidden(B_24, k1_tops_1(A_20, C_26)) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, u1_struct_0(A_20)) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.25  tff(c_1012, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1010, c_16])).
% 6.10/2.25  tff(c_1017, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_24, c_22, c_1012])).
% 6.10/2.25  tff(c_1019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_215, c_1017])).
% 6.10/2.25  tff(c_1031, plain, (![D_184]: (~r2_hidden('#skF_3', D_184) | ~r1_tarski(D_184, '#skF_4') | ~v3_pre_topc(D_184, '#skF_2') | ~m1_subset_1(D_184, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_32])).
% 6.10/2.25  tff(c_1038, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_69, c_1031])).
% 6.10/2.25  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_53, c_52, c_1038])).
% 6.10/2.25  tff(c_1049, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 6.10/2.25  tff(c_1514, plain, (![B_262, A_263, C_264]: (r2_hidden(B_262, k1_tops_1(A_263, C_264)) | ~m1_connsp_2(C_264, A_263, B_262) | ~m1_subset_1(C_264, k1_zfmisc_1(u1_struct_0(A_263))) | ~m1_subset_1(B_262, u1_struct_0(A_263)) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.25  tff(c_1518, plain, (![B_262]: (r2_hidden(B_262, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_262) | ~m1_subset_1(B_262, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_1514])).
% 6.10/2.25  tff(c_1522, plain, (![B_262]: (r2_hidden(B_262, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_262) | ~m1_subset_1(B_262, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1518])).
% 6.10/2.25  tff(c_1524, plain, (![B_265]: (r2_hidden(B_265, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_265) | ~m1_subset_1(B_265, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_1522])).
% 6.10/2.25  tff(c_1107, plain, (![A_198, B_199]: (v3_pre_topc(k1_tops_1(A_198, B_199), A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.10/2.25  tff(c_1111, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1107])).
% 6.10/2.25  tff(c_1115, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1111])).
% 6.10/2.25  tff(c_1089, plain, (![A_194, B_195]: (r1_tarski(k1_tops_1(A_194, B_195), B_195) | ~m1_subset_1(B_195, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.10/2.25  tff(c_1091, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1089])).
% 6.10/2.25  tff(c_1094, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1091])).
% 6.10/2.25  tff(c_1176, plain, (![D_215]: (~r2_hidden('#skF_3', D_215) | ~r1_tarski(D_215, '#skF_4') | ~v3_pre_topc(D_215, '#skF_2') | ~m1_subset_1(D_215, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_32])).
% 6.10/2.25  tff(c_1180, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1176])).
% 6.10/2.25  tff(c_1255, plain, (![B_228]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_228)) | ~r1_tarski(k1_tops_1('#skF_2', B_228), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_228), '#skF_2') | ~m1_subset_1(B_228, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1180])).
% 6.10/2.25  tff(c_1262, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_1255])).
% 6.10/2.25  tff(c_1268, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1115, c_1094, c_1262])).
% 6.10/2.25  tff(c_1529, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_1524, c_1268])).
% 6.10/2.25  tff(c_1543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1049, c_1529])).
% 6.10/2.25  tff(c_1544, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_42])).
% 6.10/2.25  tff(c_2001, plain, (![B_340, A_341, C_342]: (r2_hidden(B_340, k1_tops_1(A_341, C_342)) | ~m1_connsp_2(C_342, A_341, B_340) | ~m1_subset_1(C_342, k1_zfmisc_1(u1_struct_0(A_341))) | ~m1_subset_1(B_340, u1_struct_0(A_341)) | ~l1_pre_topc(A_341) | ~v2_pre_topc(A_341) | v2_struct_0(A_341))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.25  tff(c_2007, plain, (![B_340]: (r2_hidden(B_340, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_340) | ~m1_subset_1(B_340, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_2001])).
% 6.10/2.25  tff(c_2015, plain, (![B_340]: (r2_hidden(B_340, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_340) | ~m1_subset_1(B_340, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2007])).
% 6.10/2.25  tff(c_2017, plain, (![B_343]: (r2_hidden(B_343, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_343) | ~m1_subset_1(B_343, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_2015])).
% 6.10/2.25  tff(c_1599, plain, (![A_282, B_283]: (v3_pre_topc(k1_tops_1(A_282, B_283), A_282) | ~m1_subset_1(B_283, k1_zfmisc_1(u1_struct_0(A_282))) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.10/2.25  tff(c_1603, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1599])).
% 6.10/2.25  tff(c_1609, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_1603])).
% 6.10/2.25  tff(c_1580, plain, (![A_280, B_281]: (r1_tarski(k1_tops_1(A_280, B_281), B_281) | ~m1_subset_1(B_281, k1_zfmisc_1(u1_struct_0(A_280))) | ~l1_pre_topc(A_280))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.10/2.25  tff(c_1584, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_1580])).
% 6.10/2.25  tff(c_1590, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1584])).
% 6.10/2.25  tff(c_1545, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_42])).
% 6.10/2.25  tff(c_40, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_1654, plain, (![D_295]: (~r2_hidden('#skF_3', D_295) | ~r1_tarski(D_295, '#skF_4') | ~v3_pre_topc(D_295, '#skF_2') | ~m1_subset_1(D_295, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1545, c_40])).
% 6.10/2.25  tff(c_1658, plain, (![B_7]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_7)) | ~r1_tarski(k1_tops_1('#skF_2', B_7), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_7), '#skF_2') | ~m1_subset_1(B_7, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1654])).
% 6.10/2.25  tff(c_1743, plain, (![B_305]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_305)) | ~r1_tarski(k1_tops_1('#skF_2', B_305), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_305), '#skF_2') | ~m1_subset_1(B_305, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1658])).
% 6.10/2.25  tff(c_1753, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_1743])).
% 6.10/2.25  tff(c_1762, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1609, c_1590, c_1753])).
% 6.10/2.25  tff(c_2022, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2017, c_1762])).
% 6.10/2.25  tff(c_2036, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1544, c_2022])).
% 6.10/2.25  tff(c_2037, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 6.10/2.25  tff(c_2267, plain, (![B_395, A_396, C_397]: (r2_hidden(B_395, k1_tops_1(A_396, C_397)) | ~m1_connsp_2(C_397, A_396, B_395) | ~m1_subset_1(C_397, k1_zfmisc_1(u1_struct_0(A_396))) | ~m1_subset_1(B_395, u1_struct_0(A_396)) | ~l1_pre_topc(A_396) | ~v2_pre_topc(A_396) | v2_struct_0(A_396))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.25  tff(c_2271, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_2267])).
% 6.10/2.25  tff(c_2275, plain, (![B_395]: (r2_hidden(B_395, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_395) | ~m1_subset_1(B_395, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2271])).
% 6.10/2.25  tff(c_2277, plain, (![B_398]: (r2_hidden(B_398, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_398) | ~m1_subset_1(B_398, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_2275])).
% 6.10/2.25  tff(c_2068, plain, (![A_357, B_358]: (v3_pre_topc(k1_tops_1(A_357, B_358), A_357) | ~m1_subset_1(B_358, k1_zfmisc_1(u1_struct_0(A_357))) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.10/2.25  tff(c_2070, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2068])).
% 6.10/2.25  tff(c_2073, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2070])).
% 6.10/2.25  tff(c_2053, plain, (![A_352, B_353]: (r1_tarski(k1_tops_1(A_352, B_353), B_353) | ~m1_subset_1(B_353, k1_zfmisc_1(u1_struct_0(A_352))) | ~l1_pre_topc(A_352))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.10/2.25  tff(c_2055, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2053])).
% 6.10/2.25  tff(c_2058, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2055])).
% 6.10/2.25  tff(c_2083, plain, (![A_360, B_361]: (m1_subset_1(k1_tops_1(A_360, B_361), k1_zfmisc_1(u1_struct_0(A_360))) | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0(A_360))) | ~l1_pre_topc(A_360))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.25  tff(c_2038, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 6.10/2.25  tff(c_36, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_2074, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2038, c_36])).
% 6.10/2.25  tff(c_2087, plain, (![B_361]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_361)) | ~r1_tarski(k1_tops_1('#skF_2', B_361), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_361), '#skF_2') | ~m1_subset_1(B_361, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2083, c_2074])).
% 6.10/2.25  tff(c_2186, plain, (![B_385]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_385)) | ~r1_tarski(k1_tops_1('#skF_2', B_385), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_385), '#skF_2') | ~m1_subset_1(B_385, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2087])).
% 6.10/2.25  tff(c_2193, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_2186])).
% 6.10/2.25  tff(c_2199, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2073, c_2058, c_2193])).
% 6.10/2.25  tff(c_2280, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_2277, c_2199])).
% 6.10/2.25  tff(c_2290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2037, c_2280])).
% 6.10/2.25  tff(c_2291, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 6.10/2.25  tff(c_3259, plain, (![B_573, A_574, C_575]: (r2_hidden(B_573, k1_tops_1(A_574, C_575)) | ~m1_connsp_2(C_575, A_574, B_573) | ~m1_subset_1(C_575, k1_zfmisc_1(u1_struct_0(A_574))) | ~m1_subset_1(B_573, u1_struct_0(A_574)) | ~l1_pre_topc(A_574) | ~v2_pre_topc(A_574) | v2_struct_0(A_574))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.25  tff(c_3263, plain, (![B_573]: (r2_hidden(B_573, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_573) | ~m1_subset_1(B_573, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_3259])).
% 6.10/2.25  tff(c_3267, plain, (![B_573]: (r2_hidden(B_573, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_573) | ~m1_subset_1(B_573, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_3263])).
% 6.10/2.25  tff(c_3269, plain, (![B_576]: (r2_hidden(B_576, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_576) | ~m1_subset_1(B_576, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_30, c_3267])).
% 6.10/2.25  tff(c_2959, plain, (![A_521, B_522]: (v3_pre_topc(k1_tops_1(A_521, B_522), A_521) | ~m1_subset_1(B_522, k1_zfmisc_1(u1_struct_0(A_521))) | ~l1_pre_topc(A_521) | ~v2_pre_topc(A_521))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.10/2.25  tff(c_2961, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2959])).
% 6.10/2.25  tff(c_2964, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_2961])).
% 6.10/2.25  tff(c_2317, plain, (![A_410, B_411]: (r1_tarski(k1_tops_1(A_410, B_411), B_411) | ~m1_subset_1(B_411, k1_zfmisc_1(u1_struct_0(A_410))) | ~l1_pre_topc(A_410))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.10/2.25  tff(c_2319, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_22, c_2317])).
% 6.10/2.25  tff(c_2322, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2319])).
% 6.10/2.25  tff(c_2965, plain, (![A_523, B_524]: (m1_subset_1(k1_tops_1(A_523, B_524), k1_zfmisc_1(u1_struct_0(A_523))) | ~m1_subset_1(B_524, k1_zfmisc_1(u1_struct_0(A_523))) | ~l1_pre_topc(A_523))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.10/2.25  tff(c_2292, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 6.10/2.25  tff(c_44, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.10/2.25  tff(c_2935, plain, (![D_52]: (~r2_hidden('#skF_3', D_52) | ~r1_tarski(D_52, '#skF_4') | ~v3_pre_topc(D_52, '#skF_2') | ~m1_subset_1(D_52, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_2292, c_44])).
% 6.10/2.25  tff(c_2971, plain, (![B_524]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_524)) | ~r1_tarski(k1_tops_1('#skF_2', B_524), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_524), '#skF_2') | ~m1_subset_1(B_524, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_2965, c_2935])).
% 6.10/2.25  tff(c_3076, plain, (![B_544]: (~r2_hidden('#skF_3', k1_tops_1('#skF_2', B_544)) | ~r1_tarski(k1_tops_1('#skF_2', B_544), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', B_544), '#skF_2') | ~m1_subset_1(B_544, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2971])).
% 6.10/2.25  tff(c_3083, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_3076])).
% 6.10/2.25  tff(c_3089, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2964, c_2322, c_3083])).
% 6.10/2.25  tff(c_3272, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_3269, c_3089])).
% 6.10/2.25  tff(c_3282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2291, c_3272])).
% 6.10/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.25  
% 6.10/2.25  Inference rules
% 6.10/2.25  ----------------------
% 6.10/2.25  #Ref     : 0
% 6.10/2.25  #Sup     : 691
% 6.10/2.25  #Fact    : 0
% 6.10/2.25  #Define  : 0
% 6.10/2.25  #Split   : 25
% 6.10/2.25  #Chain   : 0
% 6.10/2.25  #Close   : 0
% 6.10/2.25  
% 6.10/2.25  Ordering : KBO
% 6.10/2.25  
% 6.10/2.25  Simplification rules
% 6.10/2.25  ----------------------
% 6.10/2.25  #Subsume      : 173
% 6.10/2.25  #Demod        : 352
% 6.10/2.25  #Tautology    : 108
% 6.10/2.25  #SimpNegUnit  : 30
% 6.10/2.25  #BackRed      : 0
% 6.10/2.25  
% 6.10/2.25  #Partial instantiations: 0
% 6.10/2.25  #Strategies tried      : 1
% 6.10/2.25  
% 6.10/2.25  Timing (in seconds)
% 6.10/2.25  ----------------------
% 6.10/2.25  Preprocessing        : 0.37
% 6.10/2.25  Parsing              : 0.21
% 6.10/2.25  CNF conversion       : 0.03
% 6.10/2.25  Main loop            : 1.07
% 6.10/2.25  Inferencing          : 0.38
% 6.10/2.25  Reduction            : 0.32
% 6.10/2.25  Demodulation         : 0.22
% 6.10/2.25  BG Simplification    : 0.03
% 6.10/2.25  Subsumption          : 0.27
% 6.10/2.25  Abstraction          : 0.04
% 6.10/2.25  MUC search           : 0.00
% 6.10/2.25  Cooper               : 0.00
% 6.10/2.25  Total                : 1.50
% 6.10/2.25  Index Insertion      : 0.00
% 6.10/2.25  Index Deletion       : 0.00
% 6.10/2.25  Index Matching       : 0.00
% 6.10/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
