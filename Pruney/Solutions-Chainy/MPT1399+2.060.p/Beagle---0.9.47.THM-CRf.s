%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:27 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 292 expanded)
%              Number of leaves         :   40 ( 114 expanded)
%              Depth                    :   13
%              Number of atoms          :  173 ( 859 expanded)
%              Number of equality atoms :   32 ( 141 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_137,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_34,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_86,axiom,(
    ! [A] :
      ( ~ ( ? [B] :
              ( B != k1_xboole_0
              & r2_hidden(B,A) )
          & k3_tarski(A) = k1_xboole_0 )
      & ~ ( k3_tarski(A) != k1_xboole_0
          & ! [B] :
              ~ ( B != k1_xboole_0
                & r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_orders_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_65,plain,(
    ! [A_2] : r1_tarski('#skF_5',A_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_48,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_67,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_24,plain,(
    ! [A_13] :
      ( v4_pre_topc(k2_struct_0(A_13),A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_3] : k3_tarski(k1_zfmisc_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [A_40] :
      ( u1_struct_0(A_40) = k2_struct_0(A_40)
      | ~ l1_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_121,plain,(
    ! [A_44] :
      ( u1_struct_0(A_44) = k2_struct_0(A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(resolution,[status(thm)],[c_22,c_100])).

tff(c_125,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_121])).

tff(c_231,plain,(
    ! [A_64] :
      ( m1_subset_1('#skF_2'(A_64),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_237,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_231])).

tff(c_242,plain,
    ( m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_237])).

tff(c_243,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_242])).

tff(c_177,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,B_55)
      | v1_xboole_0(B_55)
      | ~ m1_subset_1(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_14,B_17] :
      ( k3_tarski(A_14) != k1_xboole_0
      | ~ r2_hidden(B_17,A_14)
      | k1_xboole_0 = B_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_63,plain,(
    ! [A_14,B_17] :
      ( k3_tarski(A_14) != '#skF_5'
      | ~ r2_hidden(B_17,A_14)
      | B_17 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_26])).

tff(c_184,plain,(
    ! [B_55,A_54] :
      ( k3_tarski(B_55) != '#skF_5'
      | A_54 = '#skF_5'
      | v1_xboole_0(B_55)
      | ~ m1_subset_1(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_177,c_63])).

tff(c_258,plain,
    ( k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_3'))) != '#skF_5'
    | '#skF_2'('#skF_3') = '#skF_5'
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_243,c_184])).

tff(c_270,plain,
    ( k2_struct_0('#skF_3') != '#skF_5'
    | '#skF_2'('#skF_3') = '#skF_5'
    | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_258])).

tff(c_271,plain,
    ( k2_struct_0('#skF_3') != '#skF_5'
    | '#skF_2'('#skF_3') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_270])).

tff(c_275,plain,(
    k2_struct_0('#skF_3') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_271])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_127,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_46])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_32,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_64,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_56,plain,(
    ! [D_32] :
      ( r2_hidden('#skF_4',D_32)
      | ~ r2_hidden(D_32,'#skF_5')
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_133,plain,(
    ! [D_45] :
      ( r2_hidden('#skF_4',D_45)
      | ~ r2_hidden(D_45,'#skF_5')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_56])).

tff(c_138,plain,
    ( r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_133])).

tff(c_192,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_54,plain,(
    ! [D_32] :
      ( r2_hidden(D_32,'#skF_5')
      | ~ r2_hidden('#skF_4',D_32)
      | ~ v4_pre_topc(D_32,'#skF_3')
      | ~ v3_pre_topc(D_32,'#skF_3')
      | ~ m1_subset_1(D_32,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_245,plain,(
    ! [D_65] :
      ( r2_hidden(D_65,'#skF_5')
      | ~ r2_hidden('#skF_4',D_65)
      | ~ v4_pre_topc(D_65,'#skF_3')
      | ~ v3_pre_topc(D_65,'#skF_3')
      | ~ m1_subset_1(D_65,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_54])).

tff(c_249,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_245])).

tff(c_252,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_249])).

tff(c_289,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_292,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_289])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_292])).

tff(c_297,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_299,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_297])).

tff(c_302,plain,
    ( v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_299])).

tff(c_305,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_302])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_66,plain,(
    ! [A_1] :
      ( A_1 = '#skF_5'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_310,plain,(
    k2_struct_0('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_305,c_66])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_310])).

tff(c_315,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_297])).

tff(c_327,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_315])).

tff(c_331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_327])).

tff(c_332,plain,(
    '#skF_2'('#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_271])).

tff(c_38,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0('#skF_2'(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_347,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_38])).

tff(c_360,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_67,c_347])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_360])).

tff(c_364,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_379,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_364,c_18])).

tff(c_386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:14:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  
% 2.49/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.32  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.49/1.32  
% 2.49/1.32  %Foreground sorts:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Background operators:
% 2.49/1.32  
% 2.49/1.32  
% 2.49/1.32  %Foreground operators:
% 2.49/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.49/1.32  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.49/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.49/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.49/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.49/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.49/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.32  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.49/1.32  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.49/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.49/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.49/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.49/1.32  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.49/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.49/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.49/1.32  
% 2.49/1.34  tff(f_137, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.49/1.34  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.49/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.49/1.34  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.49/1.34  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.49/1.34  tff(f_34, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.49/1.34  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.49/1.34  tff(f_56, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.49/1.34  tff(f_109, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.49/1.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.49/1.34  tff(f_86, axiom, (![A]: (~((?[B]: (~(B = k1_xboole_0) & r2_hidden(B, A))) & (k3_tarski(A) = k1_xboole_0)) & ~(~(k3_tarski(A) = k1_xboole_0) & (![B]: ~(~(B = k1_xboole_0) & r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_orders_1)).
% 2.49/1.34  tff(f_92, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 2.49/1.34  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.49/1.34  tff(f_38, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.49/1.34  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.49/1.34  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.49/1.34  tff(c_42, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_6, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.34  tff(c_65, plain, (![A_2]: (r1_tarski('#skF_5', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6])).
% 2.49/1.34  tff(c_52, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_50, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_48, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.49/1.34  tff(c_67, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.49/1.34  tff(c_24, plain, (![A_13]: (v4_pre_topc(k2_struct_0(A_13), A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.49/1.34  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.34  tff(c_8, plain, (![A_3]: (k3_tarski(k1_zfmisc_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.49/1.34  tff(c_22, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.34  tff(c_100, plain, (![A_40]: (u1_struct_0(A_40)=k2_struct_0(A_40) | ~l1_struct_0(A_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.49/1.34  tff(c_121, plain, (![A_44]: (u1_struct_0(A_44)=k2_struct_0(A_44) | ~l1_pre_topc(A_44))), inference(resolution, [status(thm)], [c_22, c_100])).
% 2.49/1.34  tff(c_125, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_121])).
% 2.49/1.34  tff(c_231, plain, (![A_64]: (m1_subset_1('#skF_2'(A_64), k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.49/1.34  tff(c_237, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_125, c_231])).
% 2.49/1.34  tff(c_242, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_237])).
% 2.49/1.34  tff(c_243, plain, (m1_subset_1('#skF_2'('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_242])).
% 2.49/1.34  tff(c_177, plain, (![A_54, B_55]: (r2_hidden(A_54, B_55) | v1_xboole_0(B_55) | ~m1_subset_1(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.34  tff(c_26, plain, (![A_14, B_17]: (k3_tarski(A_14)!=k1_xboole_0 | ~r2_hidden(B_17, A_14) | k1_xboole_0=B_17)), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.49/1.34  tff(c_63, plain, (![A_14, B_17]: (k3_tarski(A_14)!='#skF_5' | ~r2_hidden(B_17, A_14) | B_17='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_26])).
% 2.49/1.34  tff(c_184, plain, (![B_55, A_54]: (k3_tarski(B_55)!='#skF_5' | A_54='#skF_5' | v1_xboole_0(B_55) | ~m1_subset_1(A_54, B_55))), inference(resolution, [status(thm)], [c_177, c_63])).
% 2.49/1.34  tff(c_258, plain, (k3_tarski(k1_zfmisc_1(k2_struct_0('#skF_3')))!='#skF_5' | '#skF_2'('#skF_3')='#skF_5' | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_243, c_184])).
% 2.49/1.34  tff(c_270, plain, (k2_struct_0('#skF_3')!='#skF_5' | '#skF_2'('#skF_3')='#skF_5' | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_258])).
% 2.49/1.34  tff(c_271, plain, (k2_struct_0('#skF_3')!='#skF_5' | '#skF_2'('#skF_3')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_14, c_270])).
% 2.49/1.34  tff(c_275, plain, (k2_struct_0('#skF_3')!='#skF_5'), inference(splitLeft, [status(thm)], [c_271])).
% 2.49/1.34  tff(c_46, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_127, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_46])).
% 2.49/1.34  tff(c_16, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.49/1.34  tff(c_32, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.49/1.34  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.34  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.49/1.34  tff(c_64, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.49/1.34  tff(c_56, plain, (![D_32]: (r2_hidden('#skF_4', D_32) | ~r2_hidden(D_32, '#skF_5') | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_133, plain, (![D_45]: (r2_hidden('#skF_4', D_45) | ~r2_hidden(D_45, '#skF_5') | ~m1_subset_1(D_45, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_56])).
% 2.49/1.34  tff(c_138, plain, (r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_64, c_133])).
% 2.49/1.34  tff(c_192, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_138])).
% 2.49/1.34  tff(c_54, plain, (![D_32]: (r2_hidden(D_32, '#skF_5') | ~r2_hidden('#skF_4', D_32) | ~v4_pre_topc(D_32, '#skF_3') | ~v3_pre_topc(D_32, '#skF_3') | ~m1_subset_1(D_32, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.49/1.34  tff(c_245, plain, (![D_65]: (r2_hidden(D_65, '#skF_5') | ~r2_hidden('#skF_4', D_65) | ~v4_pre_topc(D_65, '#skF_3') | ~v3_pre_topc(D_65, '#skF_3') | ~m1_subset_1(D_65, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_54])).
% 2.49/1.34  tff(c_249, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_64, c_245])).
% 2.49/1.34  tff(c_252, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_192, c_249])).
% 2.49/1.34  tff(c_289, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_252])).
% 2.49/1.34  tff(c_292, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_32, c_289])).
% 2.49/1.34  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_292])).
% 2.49/1.34  tff(c_297, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_252])).
% 2.49/1.34  tff(c_299, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_297])).
% 2.49/1.34  tff(c_302, plain, (v1_xboole_0(k2_struct_0('#skF_3')) | ~m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_16, c_299])).
% 2.49/1.34  tff(c_305, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_302])).
% 2.49/1.34  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.49/1.34  tff(c_66, plain, (![A_1]: (A_1='#skF_5' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 2.49/1.34  tff(c_310, plain, (k2_struct_0('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_305, c_66])).
% 2.49/1.34  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_310])).
% 2.49/1.34  tff(c_315, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_297])).
% 2.49/1.34  tff(c_327, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_24, c_315])).
% 2.49/1.34  tff(c_331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_327])).
% 2.49/1.34  tff(c_332, plain, ('#skF_2'('#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_271])).
% 2.49/1.34  tff(c_38, plain, (![A_19]: (~v1_xboole_0('#skF_2'(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.49/1.34  tff(c_347, plain, (~v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_332, c_38])).
% 2.49/1.34  tff(c_360, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_67, c_347])).
% 2.49/1.34  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_360])).
% 2.49/1.34  tff(c_364, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_138])).
% 2.49/1.34  tff(c_18, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.49/1.34  tff(c_379, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_364, c_18])).
% 2.49/1.34  tff(c_386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_379])).
% 2.49/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.34  
% 2.49/1.34  Inference rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Ref     : 0
% 2.49/1.34  #Sup     : 59
% 2.49/1.34  #Fact    : 0
% 2.49/1.34  #Define  : 0
% 2.49/1.34  #Split   : 7
% 2.49/1.34  #Chain   : 0
% 2.49/1.34  #Close   : 0
% 2.49/1.34  
% 2.49/1.34  Ordering : KBO
% 2.49/1.34  
% 2.49/1.34  Simplification rules
% 2.49/1.34  ----------------------
% 2.49/1.34  #Subsume      : 7
% 2.49/1.34  #Demod        : 45
% 2.49/1.34  #Tautology    : 22
% 2.49/1.34  #SimpNegUnit  : 12
% 2.49/1.34  #BackRed      : 3
% 2.49/1.34  
% 2.49/1.34  #Partial instantiations: 0
% 2.49/1.34  #Strategies tried      : 1
% 2.49/1.34  
% 2.49/1.34  Timing (in seconds)
% 2.49/1.34  ----------------------
% 2.49/1.34  Preprocessing        : 0.33
% 2.49/1.34  Parsing              : 0.18
% 2.49/1.34  CNF conversion       : 0.02
% 2.49/1.34  Main loop            : 0.23
% 2.49/1.34  Inferencing          : 0.08
% 2.49/1.34  Reduction            : 0.07
% 2.49/1.34  Demodulation         : 0.05
% 2.49/1.34  BG Simplification    : 0.01
% 2.49/1.34  Subsumption          : 0.03
% 2.49/1.34  Abstraction          : 0.01
% 2.49/1.34  MUC search           : 0.00
% 2.49/1.34  Cooper               : 0.00
% 2.49/1.34  Total                : 0.59
% 2.49/1.34  Index Insertion      : 0.00
% 2.49/1.34  Index Deletion       : 0.00
% 2.49/1.34  Index Matching       : 0.00
% 2.49/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
