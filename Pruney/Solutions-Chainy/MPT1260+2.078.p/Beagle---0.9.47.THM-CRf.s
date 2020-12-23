%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:10 EST 2020

% Result     : Theorem 18.36s
% Output     : CNFRefutation 18.36s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 467 expanded)
%              Number of leaves         :   32 ( 171 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 (1296 expanded)
%              Number of equality atoms :   45 ( 332 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_62,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_113,plain,(
    ~ v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_50,plain,(
    ! [C_39,A_27,D_41,B_35] :
      ( v3_pre_topc(C_39,A_27)
      | k1_tops_1(A_27,C_39) != C_39
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8332,plain,(
    ! [D_278,B_279] :
      ( ~ m1_subset_1(D_278,k1_zfmisc_1(u1_struct_0(B_279)))
      | ~ l1_pre_topc(B_279) ) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_8335,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_8332])).

tff(c_8339,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_8335])).

tff(c_9718,plain,(
    ! [C_290,A_291] :
      ( v3_pre_topc(C_290,A_291)
      | k1_tops_1(A_291,C_290) != C_290
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291) ) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_9724,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6'
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_9718])).

tff(c_9728,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_9724])).

tff(c_9729,plain,(
    k1_tops_1('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_9728])).

tff(c_140,plain,(
    ! [A_70,B_71,C_72] :
      ( k7_subset_1(A_70,B_71,C_72) = k4_xboole_0(B_71,C_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_143,plain,(
    ! [C_72] : k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',C_72) = k4_xboole_0('#skF_6',C_72) ),
    inference(resolution,[status(thm)],[c_56,c_140])).

tff(c_582,plain,(
    ! [A_115,B_116] :
      ( k7_subset_1(u1_struct_0(A_115),B_116,k2_tops_1(A_115,B_116)) = k1_tops_1(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_586,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),'#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_582])).

tff(c_590,plain,(
    k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = k1_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_143,c_586])).

tff(c_36,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden('#skF_3'(A_7,B_8,C_9),A_7)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2235,plain,(
    ! [A_177,B_178,C_179] :
      ( r2_hidden('#skF_3'(A_177,B_178,C_179),A_177)
      | r2_hidden('#skF_4'(A_177,B_178,C_179),B_178)
      | ~ r2_hidden('#skF_4'(A_177,B_178,C_179),A_177)
      | k4_xboole_0(A_177,B_178) = C_179 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2268,plain,(
    ! [C_9,B_8] :
      ( r2_hidden('#skF_4'(C_9,B_8,C_9),B_8)
      | r2_hidden('#skF_3'(C_9,B_8,C_9),C_9)
      | k4_xboole_0(C_9,B_8) = C_9 ) ),
    inference(resolution,[status(thm)],[c_36,c_2235])).

tff(c_158,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k2_pre_topc(A_74,B_75),k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(u1_struct_0(A_74)))
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_42,plain,(
    ! [A_17,B_18,C_19] :
      ( k7_subset_1(A_17,B_18,C_19) = k4_xboole_0(B_18,C_19)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10539,plain,(
    ! [A_306,B_307,C_308] :
      ( k7_subset_1(u1_struct_0(A_306),k2_pre_topc(A_306,B_307),C_308) = k4_xboole_0(k2_pre_topc(A_306,B_307),C_308)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ l1_pre_topc(A_306) ) ),
    inference(resolution,[status(thm)],[c_158,c_42])).

tff(c_10543,plain,(
    ! [C_308] :
      ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_308) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_308)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_10539])).

tff(c_10548,plain,(
    ! [C_309] : k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),C_309) = k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),C_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10543])).

tff(c_68,plain,
    ( v3_pre_topc('#skF_6','#skF_5')
    | k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_153,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_68])).

tff(c_10558,plain,(
    k4_xboole_0(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_10548,c_153])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( ~ r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k4_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10597,plain,(
    ! [D_310] :
      ( ~ r2_hidden(D_310,'#skF_6')
      | ~ r2_hidden(D_310,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10558,c_22])).

tff(c_40740,plain,(
    ! [C_566] :
      ( ~ r2_hidden('#skF_4'(C_566,k2_tops_1('#skF_5','#skF_6'),C_566),'#skF_6')
      | r2_hidden('#skF_3'(C_566,k2_tops_1('#skF_5','#skF_6'),C_566),C_566)
      | k4_xboole_0(C_566,k2_tops_1('#skF_5','#skF_6')) = C_566 ) ),
    inference(resolution,[status(thm)],[c_2268,c_10597])).

tff(c_40747,plain,
    ( r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_36,c_40740])).

tff(c_40752,plain,
    ( r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_40747])).

tff(c_40753,plain,(
    r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_9729,c_40752])).

tff(c_32,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),C_9)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ r2_hidden('#skF_3'(A_7,B_8,C_9),C_9)
      | r2_hidden('#skF_4'(A_7,B_8,C_9),B_8)
      | ~ r2_hidden('#skF_4'(A_7,B_8,C_9),A_7)
      | k4_xboole_0(A_7,B_8) = C_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40762,plain,
    ( r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),k2_tops_1('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_40753,c_26])).

tff(c_40774,plain,
    ( r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),k2_tops_1('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_40762])).

tff(c_40775,plain,
    ( r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),k2_tops_1('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_9729,c_40774])).

tff(c_41208,plain,(
    ~ r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_40775])).

tff(c_41214,plain,
    ( ~ r2_hidden('#skF_3'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6')
    | k4_xboole_0('#skF_6',k2_tops_1('#skF_5','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_32,c_41208])).

tff(c_41220,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_590,c_40753,c_41214])).

tff(c_41222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9729,c_41220])).

tff(c_41224,plain,(
    r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_40775])).

tff(c_41223,plain,(
    r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),k2_tops_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_40775])).

tff(c_10587,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_6')
      | ~ r2_hidden(D_12,k2_tops_1('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10558,c_22])).

tff(c_41257,plain,(
    ~ r2_hidden('#skF_4'('#skF_6',k2_tops_1('#skF_5','#skF_6'),'#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_41223,c_10587])).

tff(c_41273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41224,c_41257])).

tff(c_41274,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') != k2_tops_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_41275,plain,(
    v3_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_52,plain,(
    ! [B_35,D_41,C_39,A_27] :
      ( k1_tops_1(B_35,D_41) = D_41
      | ~ v3_pre_topc(D_41,B_35)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0(B_35)))
      | ~ m1_subset_1(C_39,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48135,plain,(
    ! [C_775,A_776] :
      ( ~ m1_subset_1(C_775,k1_zfmisc_1(u1_struct_0(A_776)))
      | ~ l1_pre_topc(A_776)
      | ~ v2_pre_topc(A_776) ) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48141,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_48135])).

tff(c_48146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_48141])).

tff(c_48609,plain,(
    ! [B_783,D_784] :
      ( k1_tops_1(B_783,D_784) = D_784
      | ~ v3_pre_topc(D_784,B_783)
      | ~ m1_subset_1(D_784,k1_zfmisc_1(u1_struct_0(B_783)))
      | ~ l1_pre_topc(B_783) ) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48615,plain,
    ( k1_tops_1('#skF_5','#skF_6') = '#skF_6'
    | ~ v3_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_48609])).

tff(c_48619,plain,(
    k1_tops_1('#skF_5','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_41275,c_48615])).

tff(c_48,plain,(
    ! [A_24,B_26] :
      ( k7_subset_1(u1_struct_0(A_24),k2_pre_topc(A_24,B_26),k1_tops_1(A_24,B_26)) = k2_tops_1(A_24,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48632,plain,
    ( k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48619,c_48])).

tff(c_48636,plain,(
    k7_subset_1(u1_struct_0('#skF_5'),k2_pre_topc('#skF_5','#skF_6'),'#skF_6') = k2_tops_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_48632])).

tff(c_48638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41274,c_48636])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.36/9.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.36/9.68  
% 18.36/9.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.36/9.69  %$ v3_pre_topc > r2_hidden > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 18.36/9.69  
% 18.36/9.69  %Foreground sorts:
% 18.36/9.69  
% 18.36/9.69  
% 18.36/9.69  %Background operators:
% 18.36/9.69  
% 18.36/9.69  
% 18.36/9.69  %Foreground operators:
% 18.36/9.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.36/9.69  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 18.36/9.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.36/9.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.36/9.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.36/9.69  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 18.36/9.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.36/9.69  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 18.36/9.69  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.36/9.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.36/9.69  tff('#skF_5', type, '#skF_5': $i).
% 18.36/9.69  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 18.36/9.69  tff('#skF_6', type, '#skF_6': $i).
% 18.36/9.69  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 18.36/9.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.36/9.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.36/9.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.36/9.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 18.36/9.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.36/9.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 18.36/9.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.36/9.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.36/9.69  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 18.36/9.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.36/9.69  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.36/9.69  
% 18.36/9.70  tff(f_107, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_tops_1)).
% 18.36/9.70  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_tops_1)).
% 18.36/9.70  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 18.36/9.70  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 18.36/9.70  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 18.36/9.70  tff(f_60, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 18.36/9.70  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 18.36/9.70  tff(c_62, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.36/9.70  tff(c_113, plain, (~v3_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 18.36/9.70  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.36/9.70  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.36/9.70  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.36/9.70  tff(c_50, plain, (![C_39, A_27, D_41, B_35]: (v3_pre_topc(C_39, A_27) | k1_tops_1(A_27, C_39)!=C_39 | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0(B_35))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.36/9.70  tff(c_8332, plain, (![D_278, B_279]: (~m1_subset_1(D_278, k1_zfmisc_1(u1_struct_0(B_279))) | ~l1_pre_topc(B_279))), inference(splitLeft, [status(thm)], [c_50])).
% 18.36/9.70  tff(c_8335, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_8332])).
% 18.36/9.70  tff(c_8339, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_8335])).
% 18.36/9.70  tff(c_9718, plain, (![C_290, A_291]: (v3_pre_topc(C_290, A_291) | k1_tops_1(A_291, C_290)!=C_290 | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291))), inference(splitRight, [status(thm)], [c_50])).
% 18.36/9.70  tff(c_9724, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6' | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_9718])).
% 18.36/9.70  tff(c_9728, plain, (v3_pre_topc('#skF_6', '#skF_5') | k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_9724])).
% 18.36/9.70  tff(c_9729, plain, (k1_tops_1('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_113, c_9728])).
% 18.36/9.70  tff(c_140, plain, (![A_70, B_71, C_72]: (k7_subset_1(A_70, B_71, C_72)=k4_xboole_0(B_71, C_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.36/9.70  tff(c_143, plain, (![C_72]: (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', C_72)=k4_xboole_0('#skF_6', C_72))), inference(resolution, [status(thm)], [c_56, c_140])).
% 18.36/9.70  tff(c_582, plain, (![A_115, B_116]: (k7_subset_1(u1_struct_0(A_115), B_116, k2_tops_1(A_115, B_116))=k1_tops_1(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_95])).
% 18.36/9.70  tff(c_586, plain, (k7_subset_1(u1_struct_0('#skF_5'), '#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_582])).
% 18.36/9.70  tff(c_590, plain, (k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))=k1_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_143, c_586])).
% 18.36/9.70  tff(c_36, plain, (![A_7, B_8, C_9]: (r2_hidden('#skF_3'(A_7, B_8, C_9), A_7) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.36/9.70  tff(c_2235, plain, (![A_177, B_178, C_179]: (r2_hidden('#skF_3'(A_177, B_178, C_179), A_177) | r2_hidden('#skF_4'(A_177, B_178, C_179), B_178) | ~r2_hidden('#skF_4'(A_177, B_178, C_179), A_177) | k4_xboole_0(A_177, B_178)=C_179)), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.36/9.70  tff(c_2268, plain, (![C_9, B_8]: (r2_hidden('#skF_4'(C_9, B_8, C_9), B_8) | r2_hidden('#skF_3'(C_9, B_8, C_9), C_9) | k4_xboole_0(C_9, B_8)=C_9)), inference(resolution, [status(thm)], [c_36, c_2235])).
% 18.36/9.70  tff(c_158, plain, (![A_74, B_75]: (m1_subset_1(k2_pre_topc(A_74, B_75), k1_zfmisc_1(u1_struct_0(A_74))) | ~m1_subset_1(B_75, k1_zfmisc_1(u1_struct_0(A_74))) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 18.36/9.70  tff(c_42, plain, (![A_17, B_18, C_19]: (k7_subset_1(A_17, B_18, C_19)=k4_xboole_0(B_18, C_19) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 18.36/9.70  tff(c_10539, plain, (![A_306, B_307, C_308]: (k7_subset_1(u1_struct_0(A_306), k2_pre_topc(A_306, B_307), C_308)=k4_xboole_0(k2_pre_topc(A_306, B_307), C_308) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_306))) | ~l1_pre_topc(A_306))), inference(resolution, [status(thm)], [c_158, c_42])).
% 18.36/9.70  tff(c_10543, plain, (![C_308]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_308)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_308) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_10539])).
% 18.36/9.70  tff(c_10548, plain, (![C_309]: (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), C_309)=k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), C_309))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10543])).
% 18.36/9.70  tff(c_68, plain, (v3_pre_topc('#skF_6', '#skF_5') | k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.36/9.70  tff(c_153, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_113, c_68])).
% 18.36/9.70  tff(c_10558, plain, (k4_xboole_0(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_10548, c_153])).
% 18.36/9.70  tff(c_22, plain, (![D_12, B_8, A_7]: (~r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k4_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.36/9.70  tff(c_10597, plain, (![D_310]: (~r2_hidden(D_310, '#skF_6') | ~r2_hidden(D_310, k2_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_10558, c_22])).
% 18.36/9.70  tff(c_40740, plain, (![C_566]: (~r2_hidden('#skF_4'(C_566, k2_tops_1('#skF_5', '#skF_6'), C_566), '#skF_6') | r2_hidden('#skF_3'(C_566, k2_tops_1('#skF_5', '#skF_6'), C_566), C_566) | k4_xboole_0(C_566, k2_tops_1('#skF_5', '#skF_6'))=C_566)), inference(resolution, [status(thm)], [c_2268, c_10597])).
% 18.36/9.70  tff(c_40747, plain, (r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_36, c_40740])).
% 18.36/9.70  tff(c_40752, plain, (r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_590, c_40747])).
% 18.36/9.70  tff(c_40753, plain, (r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_9729, c_40752])).
% 18.36/9.70  tff(c_32, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), C_9) | r2_hidden('#skF_4'(A_7, B_8, C_9), C_9) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.36/9.70  tff(c_26, plain, (![A_7, B_8, C_9]: (~r2_hidden('#skF_3'(A_7, B_8, C_9), C_9) | r2_hidden('#skF_4'(A_7, B_8, C_9), B_8) | ~r2_hidden('#skF_4'(A_7, B_8, C_9), A_7) | k4_xboole_0(A_7, B_8)=C_9)), inference(cnfTransformation, [status(thm)], [f_44])).
% 18.36/9.70  tff(c_40762, plain, (r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), k2_tops_1('#skF_5', '#skF_6')) | ~r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_40753, c_26])).
% 18.36/9.70  tff(c_40774, plain, (r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), k2_tops_1('#skF_5', '#skF_6')) | ~r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_590, c_40762])).
% 18.36/9.70  tff(c_40775, plain, (r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), k2_tops_1('#skF_5', '#skF_6')) | ~r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_9729, c_40774])).
% 18.36/9.70  tff(c_41208, plain, (~r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_40775])).
% 18.36/9.70  tff(c_41214, plain, (~r2_hidden('#skF_3'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6') | k4_xboole_0('#skF_6', k2_tops_1('#skF_5', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_32, c_41208])).
% 18.36/9.70  tff(c_41220, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_590, c_40753, c_41214])).
% 18.36/9.70  tff(c_41222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9729, c_41220])).
% 18.36/9.70  tff(c_41224, plain, (r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_40775])).
% 18.36/9.70  tff(c_41223, plain, (r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), k2_tops_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_40775])).
% 18.36/9.70  tff(c_10587, plain, (![D_12]: (~r2_hidden(D_12, '#skF_6') | ~r2_hidden(D_12, k2_tops_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_10558, c_22])).
% 18.36/9.70  tff(c_41257, plain, (~r2_hidden('#skF_4'('#skF_6', k2_tops_1('#skF_5', '#skF_6'), '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_41223, c_10587])).
% 18.36/9.70  tff(c_41273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41224, c_41257])).
% 18.36/9.70  tff(c_41274, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')!=k2_tops_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_62])).
% 18.36/9.70  tff(c_41275, plain, (v3_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 18.36/9.70  tff(c_52, plain, (![B_35, D_41, C_39, A_27]: (k1_tops_1(B_35, D_41)=D_41 | ~v3_pre_topc(D_41, B_35) | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0(B_35))) | ~m1_subset_1(C_39, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(B_35) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_88])).
% 18.36/9.70  tff(c_48135, plain, (![C_775, A_776]: (~m1_subset_1(C_775, k1_zfmisc_1(u1_struct_0(A_776))) | ~l1_pre_topc(A_776) | ~v2_pre_topc(A_776))), inference(splitLeft, [status(thm)], [c_52])).
% 18.36/9.70  tff(c_48141, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_48135])).
% 18.36/9.70  tff(c_48146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_48141])).
% 18.36/9.70  tff(c_48609, plain, (![B_783, D_784]: (k1_tops_1(B_783, D_784)=D_784 | ~v3_pre_topc(D_784, B_783) | ~m1_subset_1(D_784, k1_zfmisc_1(u1_struct_0(B_783))) | ~l1_pre_topc(B_783))), inference(splitRight, [status(thm)], [c_52])).
% 18.36/9.70  tff(c_48615, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6' | ~v3_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_56, c_48609])).
% 18.36/9.70  tff(c_48619, plain, (k1_tops_1('#skF_5', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_41275, c_48615])).
% 18.36/9.70  tff(c_48, plain, (![A_24, B_26]: (k7_subset_1(u1_struct_0(A_24), k2_pre_topc(A_24, B_26), k1_tops_1(A_24, B_26))=k2_tops_1(A_24, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.36/9.70  tff(c_48632, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48619, c_48])).
% 18.36/9.70  tff(c_48636, plain, (k7_subset_1(u1_struct_0('#skF_5'), k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')=k2_tops_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_48632])).
% 18.36/9.70  tff(c_48638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41274, c_48636])).
% 18.36/9.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 18.36/9.70  
% 18.36/9.70  Inference rules
% 18.36/9.70  ----------------------
% 18.36/9.70  #Ref     : 0
% 18.36/9.70  #Sup     : 14889
% 18.36/9.70  #Fact    : 0
% 18.36/9.70  #Define  : 0
% 18.36/9.70  #Split   : 6
% 18.36/9.70  #Chain   : 0
% 18.36/9.70  #Close   : 0
% 18.36/9.70  
% 18.36/9.70  Ordering : KBO
% 18.36/9.70  
% 18.36/9.70  Simplification rules
% 18.36/9.70  ----------------------
% 18.36/9.70  #Subsume      : 4907
% 18.36/9.70  #Demod        : 5157
% 18.36/9.70  #Tautology    : 771
% 18.36/9.70  #SimpNegUnit  : 13
% 18.36/9.70  #BackRed      : 14
% 18.36/9.70  
% 18.36/9.70  #Partial instantiations: 0
% 18.36/9.70  #Strategies tried      : 1
% 18.36/9.70  
% 18.36/9.70  Timing (in seconds)
% 18.36/9.70  ----------------------
% 18.36/9.71  Preprocessing        : 0.36
% 18.36/9.71  Parsing              : 0.18
% 18.36/9.71  CNF conversion       : 0.03
% 18.36/9.71  Main loop            : 8.57
% 18.36/9.71  Inferencing          : 1.28
% 18.36/9.71  Reduction            : 4.61
% 18.36/9.71  Demodulation         : 4.18
% 18.36/9.71  BG Simplification    : 0.19
% 18.36/9.71  Subsumption          : 2.03
% 18.36/9.71  Abstraction          : 0.28
% 18.36/9.71  MUC search           : 0.00
% 18.36/9.71  Cooper               : 0.00
% 18.36/9.71  Total                : 8.96
% 18.36/9.71  Index Insertion      : 0.00
% 18.36/9.71  Index Deletion       : 0.00
% 18.36/9.71  Index Matching       : 0.00
% 18.36/9.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
