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
% DateTime   : Thu Dec  3 10:19:24 EST 2020

% Result     : Theorem 9.54s
% Output     : CNFRefutation 9.54s
% Verified   : 
% Statistics : Number of formulae       :  104 (1016 expanded)
%              Number of leaves         :   36 ( 392 expanded)
%              Depth                    :   21
%              Number of atoms          :  275 (3135 expanded)
%              Number of equality atoms :   40 ( 585 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(a_2_0_orders_2,type,(
    a_2_0_orders_2: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_orders_2(A,B) = a_2_0_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,E,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_36,plain,(
    ! [A_31] :
      ( l1_struct_0(A_31)
      | ~ l1_orders_2(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    ! [A_52] :
      ( u1_struct_0(A_52) = k2_struct_0(A_52)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_84,plain,(
    ! [A_54] :
      ( u1_struct_0(A_54) = k2_struct_0(A_54)
      | ~ l1_orders_2(A_54) ) ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_88,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_84])).

tff(c_58,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_56,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_54,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_256,plain,(
    ! [A_92,B_93] :
      ( k1_orders_2(A_92,B_93) = a_2_0_orders_2(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_263,plain,(
    ! [B_93] :
      ( k1_orders_2('#skF_4',B_93) = a_2_0_orders_2('#skF_4',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_256])).

tff(c_274,plain,(
    ! [B_93] :
      ( k1_orders_2('#skF_4',B_93) = a_2_0_orders_2('#skF_4',B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_263])).

tff(c_305,plain,(
    ! [B_95] :
      ( k1_orders_2('#skF_4',B_95) = a_2_0_orders_2('#skF_4',B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_274])).

tff(c_454,plain,(
    ! [A_106] :
      ( k1_orders_2('#skF_4',A_106) = a_2_0_orders_2('#skF_4',A_106)
      | ~ r1_tarski(A_106,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_305])).

tff(c_472,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_454])).

tff(c_50,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_475,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_50])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [C_61,A_62,B_63] :
      ( r2_hidden(C_61,A_62)
      | ~ r2_hidden(C_61,B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_160,plain,(
    ! [A_80,A_81] :
      ( r2_hidden('#skF_1'(A_80),A_81)
      | ~ m1_subset_1(A_80,k1_zfmisc_1(A_81))
      | k1_xboole_0 = A_80 ) ),
    inference(resolution,[status(thm)],[c_2,c_114])).

tff(c_12,plain,(
    ! [C_9,A_6,B_7] :
      ( r2_hidden(C_9,A_6)
      | ~ r2_hidden(C_9,B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3292,plain,(
    ! [A_283,A_284,A_285] :
      ( r2_hidden('#skF_1'(A_283),A_284)
      | ~ m1_subset_1(A_285,k1_zfmisc_1(A_284))
      | ~ m1_subset_1(A_283,k1_zfmisc_1(A_285))
      | k1_xboole_0 = A_283 ) ),
    inference(resolution,[status(thm)],[c_160,c_12])).

tff(c_3331,plain,(
    ! [A_286,B_287,A_288] :
      ( r2_hidden('#skF_1'(A_286),B_287)
      | ~ m1_subset_1(A_286,k1_zfmisc_1(A_288))
      | k1_xboole_0 = A_286
      | ~ r1_tarski(A_288,B_287) ) ),
    inference(resolution,[status(thm)],[c_18,c_3292])).

tff(c_3681,plain,(
    ! [A_301,B_302,B_303] :
      ( r2_hidden('#skF_1'(A_301),B_302)
      | k1_xboole_0 = A_301
      | ~ r1_tarski(B_303,B_302)
      | ~ r1_tarski(A_301,B_303) ) ),
    inference(resolution,[status(thm)],[c_18,c_3331])).

tff(c_3707,plain,(
    ! [A_301,B_4] :
      ( r2_hidden('#skF_1'(A_301),B_4)
      | k1_xboole_0 = A_301
      | ~ r1_tarski(A_301,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_3681])).

tff(c_34,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k1_orders_2(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_orders_2(A_29)
      | ~ v5_orders_2(A_29)
      | ~ v4_orders_2(A_29)
      | ~ v3_orders_2(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_482,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_472,c_34])).

tff(c_486,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_88,c_88,c_482])).

tff(c_487,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_486])).

tff(c_532,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_487])).

tff(c_535,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_532])).

tff(c_539,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_535])).

tff(c_541,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_504,plain,(
    ! [A_107,B_108,C_109] :
      ( '#skF_2'(A_107,B_108,C_109) = A_107
      | ~ r2_hidden(A_107,a_2_0_orders_2(B_108,C_109))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(u1_struct_0(B_108)))
      | ~ l1_orders_2(B_108)
      | ~ v5_orders_2(B_108)
      | ~ v4_orders_2(B_108)
      | ~ v3_orders_2(B_108)
      | v2_struct_0(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5070,plain,(
    ! [B_359,C_360] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_359,C_360)),B_359,C_360) = '#skF_1'(a_2_0_orders_2(B_359,C_360))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(B_359)))
      | ~ l1_orders_2(B_359)
      | ~ v5_orders_2(B_359)
      | ~ v4_orders_2(B_359)
      | ~ v3_orders_2(B_359)
      | v2_struct_0(B_359)
      | a_2_0_orders_2(B_359,C_360) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_504])).

tff(c_5086,plain,(
    ! [C_360] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_360)),'#skF_4',C_360) = '#skF_1'(a_2_0_orders_2('#skF_4',C_360))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_360) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_5070])).

tff(c_5099,plain,(
    ! [C_360] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_360)),'#skF_4',C_360) = '#skF_1'(a_2_0_orders_2('#skF_4',C_360))
      | ~ m1_subset_1(C_360,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | a_2_0_orders_2('#skF_4',C_360) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_5086])).

tff(c_5170,plain,(
    ! [C_363] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',C_363)),'#skF_4',C_363) = '#skF_1'(a_2_0_orders_2('#skF_4',C_363))
      | ~ m1_subset_1(C_363,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | a_2_0_orders_2('#skF_4',C_363) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_5099])).

tff(c_5187,plain,
    ( '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_541,c_5170])).

tff(c_5211,plain,(
    '#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')) = '#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_5187])).

tff(c_3223,plain,(
    ! [B_274,E_275,A_276,C_277] :
      ( r2_orders_2(B_274,E_275,'#skF_2'(A_276,B_274,C_277))
      | ~ r2_hidden(E_275,C_277)
      | ~ m1_subset_1(E_275,u1_struct_0(B_274))
      | ~ r2_hidden(A_276,a_2_0_orders_2(B_274,C_277))
      | ~ m1_subset_1(C_277,k1_zfmisc_1(u1_struct_0(B_274)))
      | ~ l1_orders_2(B_274)
      | ~ v5_orders_2(B_274)
      | ~ v4_orders_2(B_274)
      | ~ v3_orders_2(B_274)
      | v2_struct_0(B_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3246,plain,(
    ! [B_274,E_275,A_276,A_11] :
      ( r2_orders_2(B_274,E_275,'#skF_2'(A_276,B_274,A_11))
      | ~ r2_hidden(E_275,A_11)
      | ~ m1_subset_1(E_275,u1_struct_0(B_274))
      | ~ r2_hidden(A_276,a_2_0_orders_2(B_274,A_11))
      | ~ l1_orders_2(B_274)
      | ~ v5_orders_2(B_274)
      | ~ v4_orders_2(B_274)
      | ~ v3_orders_2(B_274)
      | v2_struct_0(B_274)
      | ~ r1_tarski(A_11,u1_struct_0(B_274)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3223])).

tff(c_6337,plain,(
    ! [E_275] :
      ( r2_orders_2('#skF_4',E_275,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_275,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_275,u1_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r1_tarski(k2_struct_0('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5211,c_3246])).

tff(c_6347,plain,(
    ! [E_275] :
      ( r2_orders_2('#skF_4',E_275,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_275,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_275,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88,c_58,c_56,c_54,c_52,c_88,c_6337])).

tff(c_6348,plain,(
    ! [E_275] :
      ( r2_orders_2('#skF_4',E_275,'#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))))
      | ~ r2_hidden(E_275,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(E_275,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_6347])).

tff(c_8484,plain,(
    ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6348])).

tff(c_8487,plain,
    ( a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
    | ~ r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_3707,c_8484])).

tff(c_8499,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8487])).

tff(c_8501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_8499])).

tff(c_8503,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_6348])).

tff(c_540,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_487])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14] :
      ( m1_subset_1(A_13,C_15)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(C_15))
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_697,plain,(
    ! [A_118] :
      ( m1_subset_1(A_118,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_118,a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_540,c_20])).

tff(c_705,plain,
    ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_697])).

tff(c_709,plain,(
    m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_705])).

tff(c_3338,plain,(
    ! [B_287] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),B_287)
      | a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_287) ) ),
    inference(resolution,[status(thm)],[c_540,c_3331])).

tff(c_3588,plain,(
    ! [B_298] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),B_298)
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_298) ) ),
    inference(negUnitSimplification,[status(thm)],[c_475,c_3338])).

tff(c_9091,plain,(
    ! [A_475,B_476] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),A_475)
      | ~ m1_subset_1(B_476,k1_zfmisc_1(A_475))
      | ~ r1_tarski(k2_struct_0('#skF_4'),B_476) ) ),
    inference(resolution,[status(thm)],[c_3588,c_12])).

tff(c_9132,plain,
    ( r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_541,c_9091])).

tff(c_9166,plain,(
    r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_9132])).

tff(c_5639,plain,(
    ! [B_374,E_375,A_376,A_377] :
      ( r2_orders_2(B_374,E_375,'#skF_2'(A_376,B_374,A_377))
      | ~ r2_hidden(E_375,A_377)
      | ~ m1_subset_1(E_375,u1_struct_0(B_374))
      | ~ r2_hidden(A_376,a_2_0_orders_2(B_374,A_377))
      | ~ l1_orders_2(B_374)
      | ~ v5_orders_2(B_374)
      | ~ v4_orders_2(B_374)
      | ~ v3_orders_2(B_374)
      | v2_struct_0(B_374)
      | ~ r1_tarski(A_377,u1_struct_0(B_374)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3223])).

tff(c_28,plain,(
    ! [A_19,C_25] :
      ( ~ r2_orders_2(A_19,C_25,C_25)
      | ~ m1_subset_1(C_25,u1_struct_0(A_19))
      | ~ l1_orders_2(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_12459,plain,(
    ! [A_558,B_559,A_560] :
      ( ~ r2_hidden('#skF_2'(A_558,B_559,A_560),A_560)
      | ~ m1_subset_1('#skF_2'(A_558,B_559,A_560),u1_struct_0(B_559))
      | ~ r2_hidden(A_558,a_2_0_orders_2(B_559,A_560))
      | ~ l1_orders_2(B_559)
      | ~ v5_orders_2(B_559)
      | ~ v4_orders_2(B_559)
      | ~ v3_orders_2(B_559)
      | v2_struct_0(B_559)
      | ~ r1_tarski(A_560,u1_struct_0(B_559)) ) ),
    inference(resolution,[status(thm)],[c_5639,c_28])).

tff(c_12482,plain,
    ( ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),'#skF_4',k2_struct_0('#skF_4')),u1_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4'))),a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5211,c_12459])).

tff(c_12503,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88,c_58,c_56,c_54,c_52,c_8503,c_709,c_88,c_5211,c_9166,c_12482])).

tff(c_12505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_12503])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.54/3.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.54/3.61  
% 9.54/3.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.54/3.61  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_4 > #skF_3
% 9.54/3.61  
% 9.54/3.61  %Foreground sorts:
% 9.54/3.61  
% 9.54/3.61  
% 9.54/3.61  %Background operators:
% 9.54/3.61  
% 9.54/3.61  
% 9.54/3.61  %Foreground operators:
% 9.54/3.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.54/3.61  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 9.54/3.61  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 9.54/3.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.54/3.61  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 9.54/3.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.54/3.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.54/3.61  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 9.54/3.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.54/3.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.54/3.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.54/3.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.54/3.61  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 9.54/3.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.54/3.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.54/3.61  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 9.54/3.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.54/3.61  tff('#skF_4', type, '#skF_4': $i).
% 9.54/3.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.54/3.61  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 9.54/3.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 9.54/3.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.54/3.61  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 9.54/3.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.54/3.61  
% 9.54/3.63  tff(f_160, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 9.54/3.63  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.54/3.63  tff(f_119, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 9.54/3.63  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 9.54/3.63  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.54/3.63  tff(f_100, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 9.54/3.63  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 9.54/3.63  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 9.54/3.63  tff(f_115, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 9.54/3.63  tff(f_146, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 9.54/3.63  tff(f_60, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.54/3.63  tff(f_84, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 9.54/3.63  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.54/3.63  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.54/3.63  tff(c_52, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.54/3.63  tff(c_36, plain, (![A_31]: (l1_struct_0(A_31) | ~l1_orders_2(A_31))), inference(cnfTransformation, [status(thm)], [f_119])).
% 9.54/3.63  tff(c_72, plain, (![A_52]: (u1_struct_0(A_52)=k2_struct_0(A_52) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.54/3.63  tff(c_84, plain, (![A_54]: (u1_struct_0(A_54)=k2_struct_0(A_54) | ~l1_orders_2(A_54))), inference(resolution, [status(thm)], [c_36, c_72])).
% 9.54/3.63  tff(c_88, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_84])).
% 9.54/3.63  tff(c_58, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.54/3.63  tff(c_56, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.54/3.63  tff(c_54, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.54/3.63  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.54/3.63  tff(c_256, plain, (![A_92, B_93]: (k1_orders_2(A_92, B_93)=a_2_0_orders_2(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.54/3.63  tff(c_263, plain, (![B_93]: (k1_orders_2('#skF_4', B_93)=a_2_0_orders_2('#skF_4', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_256])).
% 9.54/3.63  tff(c_274, plain, (![B_93]: (k1_orders_2('#skF_4', B_93)=a_2_0_orders_2('#skF_4', B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_263])).
% 9.54/3.63  tff(c_305, plain, (![B_95]: (k1_orders_2('#skF_4', B_95)=a_2_0_orders_2('#skF_4', B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_274])).
% 9.54/3.63  tff(c_454, plain, (![A_106]: (k1_orders_2('#skF_4', A_106)=a_2_0_orders_2('#skF_4', A_106) | ~r1_tarski(A_106, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_18, c_305])).
% 9.54/3.63  tff(c_472, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_454])).
% 9.54/3.63  tff(c_50, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_160])).
% 9.54/3.63  tff(c_475, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_472, c_50])).
% 9.54/3.63  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.54/3.63  tff(c_114, plain, (![C_61, A_62, B_63]: (r2_hidden(C_61, A_62) | ~r2_hidden(C_61, B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.54/3.63  tff(c_160, plain, (![A_80, A_81]: (r2_hidden('#skF_1'(A_80), A_81) | ~m1_subset_1(A_80, k1_zfmisc_1(A_81)) | k1_xboole_0=A_80)), inference(resolution, [status(thm)], [c_2, c_114])).
% 9.54/3.63  tff(c_12, plain, (![C_9, A_6, B_7]: (r2_hidden(C_9, A_6) | ~r2_hidden(C_9, B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.54/3.63  tff(c_3292, plain, (![A_283, A_284, A_285]: (r2_hidden('#skF_1'(A_283), A_284) | ~m1_subset_1(A_285, k1_zfmisc_1(A_284)) | ~m1_subset_1(A_283, k1_zfmisc_1(A_285)) | k1_xboole_0=A_283)), inference(resolution, [status(thm)], [c_160, c_12])).
% 9.54/3.63  tff(c_3331, plain, (![A_286, B_287, A_288]: (r2_hidden('#skF_1'(A_286), B_287) | ~m1_subset_1(A_286, k1_zfmisc_1(A_288)) | k1_xboole_0=A_286 | ~r1_tarski(A_288, B_287))), inference(resolution, [status(thm)], [c_18, c_3292])).
% 9.54/3.63  tff(c_3681, plain, (![A_301, B_302, B_303]: (r2_hidden('#skF_1'(A_301), B_302) | k1_xboole_0=A_301 | ~r1_tarski(B_303, B_302) | ~r1_tarski(A_301, B_303))), inference(resolution, [status(thm)], [c_18, c_3331])).
% 9.54/3.63  tff(c_3707, plain, (![A_301, B_4]: (r2_hidden('#skF_1'(A_301), B_4) | k1_xboole_0=A_301 | ~r1_tarski(A_301, B_4))), inference(resolution, [status(thm)], [c_8, c_3681])).
% 9.54/3.63  tff(c_34, plain, (![A_29, B_30]: (m1_subset_1(k1_orders_2(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_orders_2(A_29) | ~v5_orders_2(A_29) | ~v4_orders_2(A_29) | ~v3_orders_2(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_115])).
% 9.54/3.63  tff(c_482, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_472, c_34])).
% 9.54/3.63  tff(c_486, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_88, c_88, c_482])).
% 9.54/3.63  tff(c_487, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_486])).
% 9.54/3.63  tff(c_532, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_487])).
% 9.54/3.63  tff(c_535, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_532])).
% 9.54/3.63  tff(c_539, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_535])).
% 9.54/3.63  tff(c_541, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_487])).
% 9.54/3.63  tff(c_504, plain, (![A_107, B_108, C_109]: ('#skF_2'(A_107, B_108, C_109)=A_107 | ~r2_hidden(A_107, a_2_0_orders_2(B_108, C_109)) | ~m1_subset_1(C_109, k1_zfmisc_1(u1_struct_0(B_108))) | ~l1_orders_2(B_108) | ~v5_orders_2(B_108) | ~v4_orders_2(B_108) | ~v3_orders_2(B_108) | v2_struct_0(B_108))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.54/3.63  tff(c_5070, plain, (![B_359, C_360]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_359, C_360)), B_359, C_360)='#skF_1'(a_2_0_orders_2(B_359, C_360)) | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(B_359))) | ~l1_orders_2(B_359) | ~v5_orders_2(B_359) | ~v4_orders_2(B_359) | ~v3_orders_2(B_359) | v2_struct_0(B_359) | a_2_0_orders_2(B_359, C_360)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_504])).
% 9.54/3.63  tff(c_5086, plain, (![C_360]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_360)), '#skF_4', C_360)='#skF_1'(a_2_0_orders_2('#skF_4', C_360)) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_360)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_88, c_5070])).
% 9.54/3.63  tff(c_5099, plain, (![C_360]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_360)), '#skF_4', C_360)='#skF_1'(a_2_0_orders_2('#skF_4', C_360)) | ~m1_subset_1(C_360, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | a_2_0_orders_2('#skF_4', C_360)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_5086])).
% 9.54/3.63  tff(c_5170, plain, (![C_363]: ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', C_363)), '#skF_4', C_363)='#skF_1'(a_2_0_orders_2('#skF_4', C_363)) | ~m1_subset_1(C_363, k1_zfmisc_1(k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', C_363)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_60, c_5099])).
% 9.54/3.63  tff(c_5187, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_541, c_5170])).
% 9.54/3.63  tff(c_5211, plain, ('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4'))='#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_475, c_5187])).
% 9.54/3.63  tff(c_3223, plain, (![B_274, E_275, A_276, C_277]: (r2_orders_2(B_274, E_275, '#skF_2'(A_276, B_274, C_277)) | ~r2_hidden(E_275, C_277) | ~m1_subset_1(E_275, u1_struct_0(B_274)) | ~r2_hidden(A_276, a_2_0_orders_2(B_274, C_277)) | ~m1_subset_1(C_277, k1_zfmisc_1(u1_struct_0(B_274))) | ~l1_orders_2(B_274) | ~v5_orders_2(B_274) | ~v4_orders_2(B_274) | ~v3_orders_2(B_274) | v2_struct_0(B_274))), inference(cnfTransformation, [status(thm)], [f_146])).
% 9.54/3.63  tff(c_3246, plain, (![B_274, E_275, A_276, A_11]: (r2_orders_2(B_274, E_275, '#skF_2'(A_276, B_274, A_11)) | ~r2_hidden(E_275, A_11) | ~m1_subset_1(E_275, u1_struct_0(B_274)) | ~r2_hidden(A_276, a_2_0_orders_2(B_274, A_11)) | ~l1_orders_2(B_274) | ~v5_orders_2(B_274) | ~v4_orders_2(B_274) | ~v3_orders_2(B_274) | v2_struct_0(B_274) | ~r1_tarski(A_11, u1_struct_0(B_274)))), inference(resolution, [status(thm)], [c_18, c_3223])).
% 9.54/3.63  tff(c_6337, plain, (![E_275]: (r2_orders_2('#skF_4', E_275, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_275, k2_struct_0('#skF_4')) | ~m1_subset_1(E_275, u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5211, c_3246])).
% 9.54/3.63  tff(c_6347, plain, (![E_275]: (r2_orders_2('#skF_4', E_275, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_275, k2_struct_0('#skF_4')) | ~m1_subset_1(E_275, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_88, c_58, c_56, c_54, c_52, c_88, c_6337])).
% 9.54/3.63  tff(c_6348, plain, (![E_275]: (r2_orders_2('#skF_4', E_275, '#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))) | ~r2_hidden(E_275, k2_struct_0('#skF_4')) | ~m1_subset_1(E_275, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_6347])).
% 9.54/3.63  tff(c_8484, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_6348])).
% 9.54/3.63  tff(c_8487, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3707, c_8484])).
% 9.54/3.63  tff(c_8499, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_8487])).
% 9.54/3.63  tff(c_8501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_475, c_8499])).
% 9.54/3.63  tff(c_8503, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_6348])).
% 9.54/3.63  tff(c_540, plain, (m1_subset_1(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_487])).
% 9.54/3.63  tff(c_20, plain, (![A_13, C_15, B_14]: (m1_subset_1(A_13, C_15) | ~m1_subset_1(B_14, k1_zfmisc_1(C_15)) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.54/3.63  tff(c_697, plain, (![A_118]: (m1_subset_1(A_118, k2_struct_0('#skF_4')) | ~r2_hidden(A_118, a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_540, c_20])).
% 9.54/3.63  tff(c_705, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_697])).
% 9.54/3.63  tff(c_709, plain, (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_475, c_705])).
% 9.54/3.63  tff(c_3338, plain, (![B_287]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), B_287) | a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0 | ~r1_tarski(k2_struct_0('#skF_4'), B_287))), inference(resolution, [status(thm)], [c_540, c_3331])).
% 9.54/3.63  tff(c_3588, plain, (![B_298]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), B_298) | ~r1_tarski(k2_struct_0('#skF_4'), B_298))), inference(negUnitSimplification, [status(thm)], [c_475, c_3338])).
% 9.54/3.63  tff(c_9091, plain, (![A_475, B_476]: (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), A_475) | ~m1_subset_1(B_476, k1_zfmisc_1(A_475)) | ~r1_tarski(k2_struct_0('#skF_4'), B_476))), inference(resolution, [status(thm)], [c_3588, c_12])).
% 9.54/3.63  tff(c_9132, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_541, c_9091])).
% 9.54/3.63  tff(c_9166, plain, (r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_9132])).
% 9.54/3.63  tff(c_5639, plain, (![B_374, E_375, A_376, A_377]: (r2_orders_2(B_374, E_375, '#skF_2'(A_376, B_374, A_377)) | ~r2_hidden(E_375, A_377) | ~m1_subset_1(E_375, u1_struct_0(B_374)) | ~r2_hidden(A_376, a_2_0_orders_2(B_374, A_377)) | ~l1_orders_2(B_374) | ~v5_orders_2(B_374) | ~v4_orders_2(B_374) | ~v3_orders_2(B_374) | v2_struct_0(B_374) | ~r1_tarski(A_377, u1_struct_0(B_374)))), inference(resolution, [status(thm)], [c_18, c_3223])).
% 9.54/3.63  tff(c_28, plain, (![A_19, C_25]: (~r2_orders_2(A_19, C_25, C_25) | ~m1_subset_1(C_25, u1_struct_0(A_19)) | ~l1_orders_2(A_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.54/3.63  tff(c_12459, plain, (![A_558, B_559, A_560]: (~r2_hidden('#skF_2'(A_558, B_559, A_560), A_560) | ~m1_subset_1('#skF_2'(A_558, B_559, A_560), u1_struct_0(B_559)) | ~r2_hidden(A_558, a_2_0_orders_2(B_559, A_560)) | ~l1_orders_2(B_559) | ~v5_orders_2(B_559) | ~v4_orders_2(B_559) | ~v3_orders_2(B_559) | v2_struct_0(B_559) | ~r1_tarski(A_560, u1_struct_0(B_559)))), inference(resolution, [status(thm)], [c_5639, c_28])).
% 9.54/3.63  tff(c_12482, plain, (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_2'('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), '#skF_4', k2_struct_0('#skF_4')), u1_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_4'), u1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5211, c_12459])).
% 9.54/3.63  tff(c_12503, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_88, c_58, c_56, c_54, c_52, c_8503, c_709, c_88, c_5211, c_9166, c_12482])).
% 9.54/3.63  tff(c_12505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_12503])).
% 9.54/3.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.54/3.63  
% 9.54/3.63  Inference rules
% 9.54/3.63  ----------------------
% 9.54/3.63  #Ref     : 0
% 9.54/3.63  #Sup     : 2745
% 9.54/3.63  #Fact    : 0
% 9.54/3.63  #Define  : 0
% 9.54/3.63  #Split   : 33
% 9.54/3.63  #Chain   : 0
% 9.54/3.63  #Close   : 0
% 9.54/3.63  
% 9.54/3.63  Ordering : KBO
% 9.54/3.63  
% 9.54/3.63  Simplification rules
% 9.54/3.63  ----------------------
% 9.54/3.63  #Subsume      : 674
% 9.54/3.63  #Demod        : 1889
% 9.54/3.63  #Tautology    : 379
% 9.54/3.63  #SimpNegUnit  : 212
% 9.54/3.63  #BackRed      : 54
% 9.54/3.63  
% 9.54/3.63  #Partial instantiations: 0
% 9.54/3.63  #Strategies tried      : 1
% 9.54/3.63  
% 9.54/3.63  Timing (in seconds)
% 9.54/3.63  ----------------------
% 9.54/3.63  Preprocessing        : 0.40
% 9.54/3.63  Parsing              : 0.17
% 9.54/3.63  CNF conversion       : 0.04
% 9.54/3.63  Main loop            : 2.39
% 9.54/3.63  Inferencing          : 0.57
% 9.54/3.63  Reduction            : 0.73
% 9.54/3.63  Demodulation         : 0.49
% 9.54/3.63  BG Simplification    : 0.08
% 9.54/3.63  Subsumption          : 0.84
% 9.54/3.63  Abstraction          : 0.10
% 9.54/3.63  MUC search           : 0.00
% 9.54/3.63  Cooper               : 0.00
% 9.54/3.63  Total                : 2.83
% 9.54/3.63  Index Insertion      : 0.00
% 9.54/3.63  Index Deletion       : 0.00
% 9.54/3.63  Index Matching       : 0.00
% 9.54/3.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
