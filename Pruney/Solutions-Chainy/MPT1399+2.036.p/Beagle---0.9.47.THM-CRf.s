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
% DateTime   : Thu Dec  3 10:24:23 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 306 expanded)
%              Number of leaves         :   39 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 819 expanded)
%              Number of equality atoms :   24 ( 129 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_37,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_57,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ! [C] :
              ( m1_subset_1(C,A)
             => ( ~ r2_hidden(C,B)
               => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6])).

tff(c_42,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_40,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [A_26] :
      ( v4_pre_topc(k2_struct_0(A_26),A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100,plain,(
    ! [B_50,A_51] :
      ( ~ r1_tarski(B_50,A_51)
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_110,plain,(
    ! [A_53] :
      ( ~ r1_tarski(A_53,'#skF_1'(A_53))
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_4,c_100])).

tff(c_115,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_110])).

tff(c_26,plain,(
    ! [A_24] :
      ( l1_struct_0(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_105,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_116,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_pre_topc(A_54) ) ),
    inference(resolution,[status(thm)],[c_26,c_105])).

tff(c_120,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_116])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_133,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_38])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16])).

tff(c_8,plain,(
    ! [A_6] : k1_subset_1(A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_6] : k1_subset_1(A_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_10,plain,(
    ! [A_7] : k2_subset_1(A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_subset_1(A_9)) = k2_subset_1(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_9] : k3_subset_1(A_9,k1_subset_1(A_9)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_59,plain,(
    ! [A_9] : k3_subset_1(A_9,'#skF_4') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_57])).

tff(c_18,plain,(
    ! [C_17,A_11,B_15] :
      ( r2_hidden(C_17,k3_subset_1(A_11,B_15))
      | r2_hidden(C_17,B_15)
      | ~ m1_subset_1(C_17,A_11)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_11))
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_263,plain,(
    ! [C_73,A_74,B_75] :
      ( r2_hidden(C_73,k3_subset_1(A_74,B_75))
      | r2_hidden(C_73,B_75)
      | ~ m1_subset_1(C_73,A_74)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74))
      | A_74 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_18])).

tff(c_275,plain,(
    ! [C_73,A_9] :
      ( r2_hidden(C_73,A_9)
      | r2_hidden(C_73,'#skF_4')
      | ~ m1_subset_1(C_73,A_9)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_9))
      | A_9 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_263])).

tff(c_297,plain,(
    ! [C_76,A_77] :
      ( r2_hidden(C_76,A_77)
      | r2_hidden(C_76,'#skF_4')
      | ~ m1_subset_1(C_76,A_77)
      | A_77 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_275])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_331,plain,(
    ! [C_76,A_77] :
      ( ~ r1_tarski('#skF_4',C_76)
      | r2_hidden(C_76,A_77)
      | ~ m1_subset_1(C_76,A_77)
      | A_77 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_297,c_22])).

tff(c_346,plain,(
    ! [C_76,A_77] :
      ( r2_hidden(C_76,A_77)
      | ~ m1_subset_1(C_76,A_77)
      | A_77 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_331])).

tff(c_32,plain,(
    ! [A_27] :
      ( v3_pre_topc(k2_struct_0(A_27),A_27)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_8] : m1_subset_1(k2_subset_1(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_56,plain,(
    ! [A_8] : m1_subset_1(A_8,k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_121,plain,(
    ! [D_55] :
      ( v4_pre_topc(D_55,'#skF_2')
      | ~ r2_hidden(D_55,'#skF_4')
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_130,plain,
    ( v4_pre_topc(u1_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(u1_struct_0('#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_121])).

tff(c_173,plain,
    ( v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_120,c_130])).

tff(c_174,plain,(
    ~ r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_46,plain,(
    ! [D_39] :
      ( r2_hidden(D_39,'#skF_4')
      | ~ r2_hidden('#skF_3',D_39)
      | ~ v4_pre_topc(D_39,'#skF_2')
      | ~ v3_pre_topc(D_39,'#skF_2')
      | ~ m1_subset_1(D_39,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_410,plain,(
    ! [D_82] :
      ( r2_hidden(D_82,'#skF_4')
      | ~ r2_hidden('#skF_3',D_82)
      | ~ v4_pre_topc(D_82,'#skF_2')
      | ~ v3_pre_topc(D_82,'#skF_2')
      | ~ m1_subset_1(D_82,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_46])).

tff(c_422,plain,
    ( r2_hidden(k2_struct_0('#skF_2'),'#skF_4')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_410])).

tff(c_433,plain,
    ( ~ r2_hidden('#skF_3',k2_struct_0('#skF_2'))
    | ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_422])).

tff(c_557,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_433])).

tff(c_560,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_557])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_560])).

tff(c_565,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_433])).

tff(c_567,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_565])).

tff(c_570,plain,
    ( ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_346,c_567])).

tff(c_573,plain,(
    k2_struct_0('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_570])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_139,plain,(
    ! [A_56] :
      ( ~ v1_xboole_0(u1_struct_0(A_56))
      | ~ l1_struct_0(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_142,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_139])).

tff(c_143,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_142])).

tff(c_145,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_148,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_145])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_148])).

tff(c_153,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_581,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_153])).

tff(c_588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_581])).

tff(c_589,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_565])).

tff(c_629,plain,
    ( ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_589])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_629])).

tff(c_635,plain,(
    r2_hidden(k2_struct_0('#skF_2'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_638,plain,(
    ~ r1_tarski('#skF_4',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_635,c_22])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:42:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.42  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_subset_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.77/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.77/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.77/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.77/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.77/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.77/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.42  
% 2.77/1.44  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.77/1.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.44  tff(f_90, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.77/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.77/1.44  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.77/1.44  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.77/1.44  tff(f_72, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.77/1.44  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.77/1.44  tff(f_35, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.77/1.44  tff(f_37, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.77/1.44  tff(f_41, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.77/1.44  tff(f_57, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_subset_1)).
% 2.77/1.44  tff(f_96, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.77/1.44  tff(f_39, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.77/1.44  tff(f_84, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.77/1.44  tff(c_34, plain, (k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.77/1.44  tff(c_60, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6])).
% 2.77/1.44  tff(c_42, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_40, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_30, plain, (![A_26]: (v4_pre_topc(k2_struct_0(A_26), A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.44  tff(c_100, plain, (![B_50, A_51]: (~r1_tarski(B_50, A_51) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.44  tff(c_110, plain, (![A_53]: (~r1_tarski(A_53, '#skF_1'(A_53)) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_4, c_100])).
% 2.77/1.44  tff(c_115, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_110])).
% 2.77/1.44  tff(c_26, plain, (![A_24]: (l1_struct_0(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.77/1.44  tff(c_105, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.77/1.44  tff(c_116, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_pre_topc(A_54))), inference(resolution, [status(thm)], [c_26, c_105])).
% 2.77/1.44  tff(c_120, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_116])).
% 2.77/1.44  tff(c_38, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_133, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_38])).
% 2.77/1.44  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.44  tff(c_54, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16])).
% 2.77/1.44  tff(c_8, plain, (![A_6]: (k1_subset_1(A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.44  tff(c_58, plain, (![A_6]: (k1_subset_1(A_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 2.77/1.44  tff(c_10, plain, (![A_7]: (k2_subset_1(A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.44  tff(c_14, plain, (![A_9]: (k3_subset_1(A_9, k1_subset_1(A_9))=k2_subset_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.44  tff(c_57, plain, (![A_9]: (k3_subset_1(A_9, k1_subset_1(A_9))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14])).
% 2.77/1.44  tff(c_59, plain, (![A_9]: (k3_subset_1(A_9, '#skF_4')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_57])).
% 2.77/1.44  tff(c_18, plain, (![C_17, A_11, B_15]: (r2_hidden(C_17, k3_subset_1(A_11, B_15)) | r2_hidden(C_17, B_15) | ~m1_subset_1(C_17, A_11) | ~m1_subset_1(B_15, k1_zfmisc_1(A_11)) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.44  tff(c_263, plain, (![C_73, A_74, B_75]: (r2_hidden(C_73, k3_subset_1(A_74, B_75)) | r2_hidden(C_73, B_75) | ~m1_subset_1(C_73, A_74) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)) | A_74='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_18])).
% 2.77/1.44  tff(c_275, plain, (![C_73, A_9]: (r2_hidden(C_73, A_9) | r2_hidden(C_73, '#skF_4') | ~m1_subset_1(C_73, A_9) | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_9)) | A_9='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_59, c_263])).
% 2.77/1.44  tff(c_297, plain, (![C_76, A_77]: (r2_hidden(C_76, A_77) | r2_hidden(C_76, '#skF_4') | ~m1_subset_1(C_76, A_77) | A_77='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_275])).
% 2.77/1.44  tff(c_22, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.77/1.44  tff(c_331, plain, (![C_76, A_77]: (~r1_tarski('#skF_4', C_76) | r2_hidden(C_76, A_77) | ~m1_subset_1(C_76, A_77) | A_77='#skF_4')), inference(resolution, [status(thm)], [c_297, c_22])).
% 2.77/1.44  tff(c_346, plain, (![C_76, A_77]: (r2_hidden(C_76, A_77) | ~m1_subset_1(C_76, A_77) | A_77='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_331])).
% 2.77/1.44  tff(c_32, plain, (![A_27]: (v3_pre_topc(k2_struct_0(A_27), A_27) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.77/1.44  tff(c_12, plain, (![A_8]: (m1_subset_1(k2_subset_1(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.44  tff(c_56, plain, (![A_8]: (m1_subset_1(A_8, k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.77/1.44  tff(c_121, plain, (![D_55]: (v4_pre_topc(D_55, '#skF_2') | ~r2_hidden(D_55, '#skF_4') | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_130, plain, (v4_pre_topc(u1_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(u1_struct_0('#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_56, c_121])).
% 2.77/1.44  tff(c_173, plain, (v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_120, c_130])).
% 2.77/1.44  tff(c_174, plain, (~r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_173])).
% 2.77/1.44  tff(c_46, plain, (![D_39]: (r2_hidden(D_39, '#skF_4') | ~r2_hidden('#skF_3', D_39) | ~v4_pre_topc(D_39, '#skF_2') | ~v3_pre_topc(D_39, '#skF_2') | ~m1_subset_1(D_39, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_410, plain, (![D_82]: (r2_hidden(D_82, '#skF_4') | ~r2_hidden('#skF_3', D_82) | ~v4_pre_topc(D_82, '#skF_2') | ~v3_pre_topc(D_82, '#skF_2') | ~m1_subset_1(D_82, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_46])).
% 2.77/1.44  tff(c_422, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_56, c_410])).
% 2.77/1.44  tff(c_433, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2')) | ~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_174, c_422])).
% 2.77/1.44  tff(c_557, plain, (~v3_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_433])).
% 2.77/1.44  tff(c_560, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_32, c_557])).
% 2.77/1.44  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_560])).
% 2.77/1.44  tff(c_565, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_433])).
% 2.77/1.44  tff(c_567, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_565])).
% 2.77/1.44  tff(c_570, plain, (~m1_subset_1('#skF_3', k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_346, c_567])).
% 2.77/1.44  tff(c_573, plain, (k2_struct_0('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_570])).
% 2.77/1.44  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 2.77/1.44  tff(c_139, plain, (![A_56]: (~v1_xboole_0(u1_struct_0(A_56)) | ~l1_struct_0(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.77/1.44  tff(c_142, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_120, c_139])).
% 2.77/1.44  tff(c_143, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_142])).
% 2.77/1.44  tff(c_145, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_143])).
% 2.77/1.44  tff(c_148, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_145])).
% 2.77/1.44  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_148])).
% 2.77/1.44  tff(c_153, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_143])).
% 2.77/1.44  tff(c_581, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_573, c_153])).
% 2.77/1.44  tff(c_588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_115, c_581])).
% 2.77/1.44  tff(c_589, plain, (~v4_pre_topc(k2_struct_0('#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_565])).
% 2.77/1.44  tff(c_629, plain, (~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_30, c_589])).
% 2.77/1.44  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_629])).
% 2.77/1.44  tff(c_635, plain, (r2_hidden(k2_struct_0('#skF_2'), '#skF_4')), inference(splitRight, [status(thm)], [c_173])).
% 2.77/1.44  tff(c_638, plain, (~r1_tarski('#skF_4', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_635, c_22])).
% 2.77/1.44  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_638])).
% 2.77/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.44  
% 2.77/1.44  Inference rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Ref     : 0
% 2.77/1.44  #Sup     : 102
% 2.77/1.44  #Fact    : 2
% 2.77/1.44  #Define  : 0
% 2.77/1.44  #Split   : 10
% 2.77/1.44  #Chain   : 0
% 2.77/1.44  #Close   : 0
% 2.77/1.44  
% 2.77/1.44  Ordering : KBO
% 2.77/1.44  
% 2.77/1.44  Simplification rules
% 2.77/1.44  ----------------------
% 2.77/1.44  #Subsume      : 33
% 2.77/1.44  #Demod        : 62
% 2.77/1.44  #Tautology    : 28
% 2.77/1.44  #SimpNegUnit  : 6
% 2.77/1.44  #BackRed      : 24
% 2.77/1.44  
% 2.77/1.44  #Partial instantiations: 0
% 2.77/1.44  #Strategies tried      : 1
% 2.77/1.44  
% 2.77/1.44  Timing (in seconds)
% 2.77/1.44  ----------------------
% 3.02/1.44  Preprocessing        : 0.30
% 3.02/1.45  Parsing              : 0.16
% 3.02/1.45  CNF conversion       : 0.02
% 3.02/1.45  Main loop            : 0.31
% 3.02/1.45  Inferencing          : 0.10
% 3.02/1.45  Reduction            : 0.10
% 3.02/1.45  Demodulation         : 0.07
% 3.02/1.45  BG Simplification    : 0.02
% 3.02/1.45  Subsumption          : 0.06
% 3.02/1.45  Abstraction          : 0.01
% 3.02/1.45  MUC search           : 0.00
% 3.02/1.45  Cooper               : 0.00
% 3.02/1.45  Total                : 0.66
% 3.02/1.45  Index Insertion      : 0.00
% 3.02/1.45  Index Deletion       : 0.00
% 3.02/1.45  Index Matching       : 0.00
% 3.02/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
