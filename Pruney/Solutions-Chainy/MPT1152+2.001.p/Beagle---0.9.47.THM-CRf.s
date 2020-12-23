%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:27 EST 2020

% Result     : Theorem 7.26s
% Output     : CNFRefutation 7.26s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 471 expanded)
%              Number of leaves         :   43 ( 177 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 (1213 expanded)
%              Number of equality atoms :   37 ( 218 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_zfmisc_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(a_2_1_orders_2,type,(
    a_2_1_orders_2: ( $i * $i ) > $i )).

tff(k2_orders_2,type,(
    k2_orders_2: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_188,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k2_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

tff(f_89,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F,G] :
                  ( ( r2_hidden(C,D)
                    & r2_hidden(D,E)
                    & r2_hidden(E,F)
                    & r2_hidden(F,G)
                    & r2_hidden(G,B) )
                 => r1_xboole_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

tff(f_147,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_orders_2(A,B) = a_2_1_orders_2(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_143,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v3_orders_2(B)
        & v4_orders_2(B)
        & v5_orders_2(B)
        & l1_orders_2(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_1_orders_2(B,C))
      <=> ? [D] :
            ( m1_subset_1(D,u1_struct_0(B))
            & A = D
            & ! [E] :
                ( m1_subset_1(E,u1_struct_0(B))
               => ( r2_hidden(E,C)
                 => r2_orders_2(B,D,E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_112,axiom,(
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

tff(c_22,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_68,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_66,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_64,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_62,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_30,plain,(
    ! [A_18] :
      ( r2_hidden('#skF_2'(A_18),A_18)
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    ! [A_54] :
      ( l1_struct_0(A_54)
      | ~ l1_orders_2(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_114,plain,(
    ! [A_78] :
      ( u1_struct_0(A_78) = k2_struct_0(A_78)
      | ~ l1_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    ! [A_83] :
      ( u1_struct_0(A_83) = k2_struct_0(A_83)
      | ~ l1_orders_2(A_83) ) ),
    inference(resolution,[status(thm)],[c_46,c_114])).

tff(c_146,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_167,plain,(
    ! [A_88] :
      ( m1_subset_1(k2_struct_0(A_88),k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_173,plain,
    ( m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_167])).

tff(c_214,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_173])).

tff(c_217,plain,(
    ~ l1_orders_2('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_214])).

tff(c_221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_217])).

tff(c_222,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_173])).

tff(c_305,plain,(
    ! [A_107,C_108,B_109] :
      ( m1_subset_1(A_107,C_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(C_108))
      | ~ r2_hidden(A_107,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_327,plain,(
    ! [A_110] :
      ( m1_subset_1(A_110,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_110,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_222,c_305])).

tff(c_341,plain,
    ( m1_subset_1('#skF_2'(k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_327])).

tff(c_343,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_348,plain,(
    u1_struct_0('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_146])).

tff(c_628,plain,(
    ! [A_133,B_134] :
      ( k2_orders_2(A_133,B_134) = a_2_1_orders_2(A_133,B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_orders_2(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_631,plain,(
    ! [B_134] :
      ( k2_orders_2('#skF_5',B_134) = a_2_1_orders_2('#skF_5',B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_xboole_0))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_628])).

tff(c_652,plain,(
    ! [B_134] :
      ( k2_orders_2('#skF_5',B_134) = a_2_1_orders_2('#skF_5',B_134)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(k1_xboole_0))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_631])).

tff(c_659,plain,(
    ! [B_135] :
      ( k2_orders_2('#skF_5',B_135) = a_2_1_orders_2('#skF_5',B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_652])).

tff(c_683,plain,(
    k2_orders_2('#skF_5',k1_xboole_0) = a_2_1_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_659])).

tff(c_60,plain,(
    k2_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_349,plain,(
    k2_orders_2('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_60])).

tff(c_684,plain,(
    a_2_1_orders_2('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_683,c_349])).

tff(c_104,plain,(
    ! [A_77] :
      ( v1_xboole_0(A_77)
      | r2_hidden('#skF_1'(A_77),A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_72,B_73] : ~ r2_hidden(A_72,k2_zfmisc_1(A_72,B_73)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_101,plain,(
    ! [A_5] : ~ r2_hidden(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_95])).

tff(c_113,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_104,c_101])).

tff(c_808,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1(k2_orders_2(A_146,B_147),k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_821,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_808])).

tff(c_830,plain,
    ( m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_22,c_348,c_348,c_821])).

tff(c_831,plain,(
    m1_subset_1(a_2_1_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_830])).

tff(c_26,plain,(
    ! [C_17,B_16,A_15] :
      ( ~ v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_841,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_15,a_2_1_orders_2('#skF_5',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_831,c_26])).

tff(c_851,plain,(
    ! [A_148] : ~ r2_hidden(A_148,a_2_1_orders_2('#skF_5',k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_841])).

tff(c_859,plain,(
    a_2_1_orders_2('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_851])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_684,c_859])).

tff(c_870,plain,(
    k2_struct_0('#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_995,plain,(
    ! [A_164,B_165] :
      ( k2_orders_2(A_164,B_165) = a_2_1_orders_2(A_164,B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_orders_2(A_164)
      | ~ v5_orders_2(A_164)
      | ~ v4_orders_2(A_164)
      | ~ v3_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1013,plain,(
    ! [B_165] :
      ( k2_orders_2('#skF_5',B_165) = a_2_1_orders_2('#skF_5',B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_995])).

tff(c_1023,plain,(
    ! [B_165] :
      ( k2_orders_2('#skF_5',B_165) = a_2_1_orders_2('#skF_5',B_165)
      | ~ m1_subset_1(B_165,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_1013])).

tff(c_1049,plain,(
    ! [B_168] :
      ( k2_orders_2('#skF_5',B_168) = a_2_1_orders_2('#skF_5',B_168)
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1023])).

tff(c_1069,plain,(
    k2_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_222,c_1049])).

tff(c_1082,plain,(
    a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_60])).

tff(c_1896,plain,(
    ! [A_212,B_213,C_214] :
      ( m1_subset_1('#skF_3'(A_212,B_213,C_214),u1_struct_0(B_213))
      | ~ r2_hidden(A_212,a_2_1_orders_2(B_213,C_214))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0(B_213)))
      | ~ l1_orders_2(B_213)
      | ~ v5_orders_2(B_213)
      | ~ v4_orders_2(B_213)
      | ~ v3_orders_2(B_213)
      | v2_struct_0(B_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_1904,plain,(
    ! [A_212,C_214] :
      ( m1_subset_1('#skF_3'(A_212,'#skF_5',C_214),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_212,a_2_1_orders_2('#skF_5',C_214))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_1896])).

tff(c_1908,plain,(
    ! [A_212,C_214] :
      ( m1_subset_1('#skF_3'(A_212,'#skF_5',C_214),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_212,a_2_1_orders_2('#skF_5',C_214))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_146,c_1904])).

tff(c_1909,plain,(
    ! [A_212,C_214] :
      ( m1_subset_1('#skF_3'(A_212,'#skF_5',C_214),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_212,a_2_1_orders_2('#skF_5',C_214))
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1908])).

tff(c_869,plain,(
    m1_subset_1('#skF_2'(k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,A_9)
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_874,plain,
    ( v1_xboole_0('#skF_2'(k2_struct_0('#skF_5')))
    | ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_869,c_20])).

tff(c_875,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r2_hidden(B_10,A_9)
      | ~ m1_subset_1(B_10,A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2576,plain,(
    ! [B_242,A_243,C_244,E_245] :
      ( r2_orders_2(B_242,'#skF_3'(A_243,B_242,C_244),E_245)
      | ~ r2_hidden(E_245,C_244)
      | ~ m1_subset_1(E_245,u1_struct_0(B_242))
      | ~ r2_hidden(A_243,a_2_1_orders_2(B_242,C_244))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(u1_struct_0(B_242)))
      | ~ l1_orders_2(B_242)
      | ~ v5_orders_2(B_242)
      | ~ v4_orders_2(B_242)
      | ~ v3_orders_2(B_242)
      | v2_struct_0(B_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2597,plain,(
    ! [A_243,C_244,E_245] :
      ( r2_orders_2('#skF_5','#skF_3'(A_243,'#skF_5',C_244),E_245)
      | ~ r2_hidden(E_245,C_244)
      | ~ m1_subset_1(E_245,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_243,a_2_1_orders_2('#skF_5',C_244))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_2576])).

tff(c_2609,plain,(
    ! [A_243,C_244,E_245] :
      ( r2_orders_2('#skF_5','#skF_3'(A_243,'#skF_5',C_244),E_245)
      | ~ r2_hidden(E_245,C_244)
      | ~ m1_subset_1(E_245,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_243,a_2_1_orders_2('#skF_5',C_244))
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_146,c_2597])).

tff(c_2751,plain,(
    ! [A_249,C_250,E_251] :
      ( r2_orders_2('#skF_5','#skF_3'(A_249,'#skF_5',C_250),E_251)
      | ~ r2_hidden(E_251,C_250)
      | ~ m1_subset_1(E_251,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_249,a_2_1_orders_2('#skF_5',C_250))
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2609])).

tff(c_4990,plain,(
    ! [A_352,E_353] :
      ( r2_orders_2('#skF_5','#skF_3'(A_352,'#skF_5',k2_struct_0('#skF_5')),E_353)
      | ~ r2_hidden(E_353,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_353,k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_352,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_222,c_2751])).

tff(c_38,plain,(
    ! [A_42,C_48] :
      ( ~ r2_orders_2(A_42,C_48,C_48)
      | ~ m1_subset_1(C_48,u1_struct_0(A_42))
      | ~ l1_orders_2(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4998,plain,(
    ! [A_352] :
      ( ~ m1_subset_1('#skF_3'(A_352,'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5')
      | ~ r2_hidden('#skF_3'(A_352,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_352,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_352,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_4990,c_38])).

tff(c_6155,plain,(
    ! [A_401] :
      ( ~ r2_hidden('#skF_3'(A_401,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_401,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_401,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_146,c_4998])).

tff(c_6164,plain,(
    ! [A_401] :
      ( ~ r2_hidden(A_401,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_3'(A_401,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | v1_xboole_0(k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_16,c_6155])).

tff(c_6172,plain,(
    ! [A_402] :
      ( ~ r2_hidden(A_402,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_3'(A_402,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_875,c_6164])).

tff(c_6182,plain,(
    ! [A_212] :
      ( ~ r2_hidden(A_212,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1909,c_6172])).

tff(c_6196,plain,(
    ! [A_403] : ~ r2_hidden(A_403,a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_6182])).

tff(c_6204,plain,(
    a_2_1_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_6196])).

tff(c_6215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1082,c_6204])).

tff(c_6217,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_119,plain,(
    ! [A_79] :
      ( r2_hidden('#skF_2'(A_79),A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_79] :
      ( ~ v1_xboole_0(A_79)
      | k1_xboole_0 = A_79 ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_6220,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6217,c_127])).

tff(c_6224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_870,c_6220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.26/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.63  
% 7.26/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.64  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_xboole_0 > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_zfmisc_1 > k2_orders_2 > a_2_1_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_4 > #skF_3
% 7.26/2.64  
% 7.26/2.64  %Foreground sorts:
% 7.26/2.64  
% 7.26/2.64  
% 7.26/2.64  %Background operators:
% 7.26/2.64  
% 7.26/2.64  
% 7.26/2.64  %Foreground operators:
% 7.26/2.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.26/2.64  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.26/2.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.26/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.26/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.26/2.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.26/2.64  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.26/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.26/2.64  tff(a_2_1_orders_2, type, a_2_1_orders_2: ($i * $i) > $i).
% 7.26/2.64  tff(k2_orders_2, type, k2_orders_2: ($i * $i) > $i).
% 7.26/2.64  tff('#skF_5', type, '#skF_5': $i).
% 7.26/2.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.26/2.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.26/2.64  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.26/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.26/2.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.26/2.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 7.26/2.64  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.26/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.26/2.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.26/2.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.26/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.26/2.64  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 7.26/2.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.26/2.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.26/2.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.26/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.26/2.64  
% 7.26/2.65  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.26/2.65  tff(f_188, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k2_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_orders_2)).
% 7.26/2.65  tff(f_89, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F, G]: (((((r2_hidden(C, D) & r2_hidden(D, E)) & r2_hidden(E, F)) & r2_hidden(F, G)) & r2_hidden(G, B)) => r1_xboole_0(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_mcart_1)).
% 7.26/2.65  tff(f_147, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 7.26/2.65  tff(f_93, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.26/2.65  tff(f_97, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 7.26/2.65  tff(f_61, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 7.26/2.65  tff(f_128, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_orders_2(A, B) = a_2_1_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_orders_2)).
% 7.26/2.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.26/2.65  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.26/2.65  tff(f_40, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 7.26/2.65  tff(f_143, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_orders_2)).
% 7.26/2.65  tff(f_68, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.26/2.65  tff(f_174, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_1_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, D, E))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 7.26/2.65  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 7.26/2.65  tff(f_112, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 7.26/2.65  tff(c_22, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.26/2.65  tff(c_70, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.26/2.65  tff(c_68, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.26/2.65  tff(c_66, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.26/2.65  tff(c_64, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.26/2.65  tff(c_62, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.26/2.65  tff(c_30, plain, (![A_18]: (r2_hidden('#skF_2'(A_18), A_18) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.26/2.65  tff(c_46, plain, (![A_54]: (l1_struct_0(A_54) | ~l1_orders_2(A_54))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.26/2.65  tff(c_114, plain, (![A_78]: (u1_struct_0(A_78)=k2_struct_0(A_78) | ~l1_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.26/2.65  tff(c_142, plain, (![A_83]: (u1_struct_0(A_83)=k2_struct_0(A_83) | ~l1_orders_2(A_83))), inference(resolution, [status(thm)], [c_46, c_114])).
% 7.26/2.65  tff(c_146, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_62, c_142])).
% 7.26/2.65  tff(c_167, plain, (![A_88]: (m1_subset_1(k2_struct_0(A_88), k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.26/2.65  tff(c_173, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_146, c_167])).
% 7.26/2.65  tff(c_214, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_173])).
% 7.26/2.65  tff(c_217, plain, (~l1_orders_2('#skF_5')), inference(resolution, [status(thm)], [c_46, c_214])).
% 7.26/2.65  tff(c_221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_217])).
% 7.26/2.65  tff(c_222, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_173])).
% 7.26/2.65  tff(c_305, plain, (![A_107, C_108, B_109]: (m1_subset_1(A_107, C_108) | ~m1_subset_1(B_109, k1_zfmisc_1(C_108)) | ~r2_hidden(A_107, B_109))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.26/2.65  tff(c_327, plain, (![A_110]: (m1_subset_1(A_110, k2_struct_0('#skF_5')) | ~r2_hidden(A_110, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_222, c_305])).
% 7.26/2.65  tff(c_341, plain, (m1_subset_1('#skF_2'(k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | k2_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_327])).
% 7.26/2.65  tff(c_343, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_341])).
% 7.26/2.65  tff(c_348, plain, (u1_struct_0('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_343, c_146])).
% 7.26/2.65  tff(c_628, plain, (![A_133, B_134]: (k2_orders_2(A_133, B_134)=a_2_1_orders_2(A_133, B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_orders_2(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.26/2.65  tff(c_631, plain, (![B_134]: (k2_orders_2('#skF_5', B_134)=a_2_1_orders_2('#skF_5', B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_348, c_628])).
% 7.26/2.65  tff(c_652, plain, (![B_134]: (k2_orders_2('#skF_5', B_134)=a_2_1_orders_2('#skF_5', B_134) | ~m1_subset_1(B_134, k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_631])).
% 7.26/2.65  tff(c_659, plain, (![B_135]: (k2_orders_2('#skF_5', B_135)=a_2_1_orders_2('#skF_5', B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(k1_xboole_0)))), inference(negUnitSimplification, [status(thm)], [c_70, c_652])).
% 7.26/2.65  tff(c_683, plain, (k2_orders_2('#skF_5', k1_xboole_0)=a_2_1_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_659])).
% 7.26/2.65  tff(c_60, plain, (k2_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_188])).
% 7.26/2.65  tff(c_349, plain, (k2_orders_2('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_343, c_60])).
% 7.26/2.65  tff(c_684, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_683, c_349])).
% 7.26/2.65  tff(c_104, plain, (![A_77]: (v1_xboole_0(A_77) | r2_hidden('#skF_1'(A_77), A_77))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.26/2.65  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.26/2.65  tff(c_95, plain, (![A_72, B_73]: (~r2_hidden(A_72, k2_zfmisc_1(A_72, B_73)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.26/2.65  tff(c_101, plain, (![A_5]: (~r2_hidden(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_95])).
% 7.26/2.65  tff(c_113, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_104, c_101])).
% 7.26/2.65  tff(c_808, plain, (![A_146, B_147]: (m1_subset_1(k2_orders_2(A_146, B_147), k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.26/2.65  tff(c_821, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_683, c_808])).
% 7.26/2.65  tff(c_830, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k1_xboole_0)) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_22, c_348, c_348, c_821])).
% 7.26/2.65  tff(c_831, plain, (m1_subset_1(a_2_1_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_70, c_830])).
% 7.26/2.65  tff(c_26, plain, (![C_17, B_16, A_15]: (~v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.26/2.65  tff(c_841, plain, (![A_15]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_15, a_2_1_orders_2('#skF_5', k1_xboole_0)))), inference(resolution, [status(thm)], [c_831, c_26])).
% 7.26/2.65  tff(c_851, plain, (![A_148]: (~r2_hidden(A_148, a_2_1_orders_2('#skF_5', k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_841])).
% 7.26/2.65  tff(c_859, plain, (a_2_1_orders_2('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_851])).
% 7.26/2.65  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_684, c_859])).
% 7.26/2.65  tff(c_870, plain, (k2_struct_0('#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_341])).
% 7.26/2.65  tff(c_995, plain, (![A_164, B_165]: (k2_orders_2(A_164, B_165)=a_2_1_orders_2(A_164, B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_orders_2(A_164) | ~v5_orders_2(A_164) | ~v4_orders_2(A_164) | ~v3_orders_2(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.26/2.65  tff(c_1013, plain, (![B_165]: (k2_orders_2('#skF_5', B_165)=a_2_1_orders_2('#skF_5', B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_995])).
% 7.26/2.65  tff(c_1023, plain, (![B_165]: (k2_orders_2('#skF_5', B_165)=a_2_1_orders_2('#skF_5', B_165) | ~m1_subset_1(B_165, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_1013])).
% 7.26/2.65  tff(c_1049, plain, (![B_168]: (k2_orders_2('#skF_5', B_168)=a_2_1_orders_2('#skF_5', B_168) | ~m1_subset_1(B_168, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_1023])).
% 7.26/2.65  tff(c_1069, plain, (k2_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_222, c_1049])).
% 7.26/2.65  tff(c_1082, plain, (a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_60])).
% 7.26/2.65  tff(c_1896, plain, (![A_212, B_213, C_214]: (m1_subset_1('#skF_3'(A_212, B_213, C_214), u1_struct_0(B_213)) | ~r2_hidden(A_212, a_2_1_orders_2(B_213, C_214)) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0(B_213))) | ~l1_orders_2(B_213) | ~v5_orders_2(B_213) | ~v4_orders_2(B_213) | ~v3_orders_2(B_213) | v2_struct_0(B_213))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.26/2.65  tff(c_1904, plain, (![A_212, C_214]: (m1_subset_1('#skF_3'(A_212, '#skF_5', C_214), k2_struct_0('#skF_5')) | ~r2_hidden(A_212, a_2_1_orders_2('#skF_5', C_214)) | ~m1_subset_1(C_214, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_1896])).
% 7.26/2.65  tff(c_1908, plain, (![A_212, C_214]: (m1_subset_1('#skF_3'(A_212, '#skF_5', C_214), k2_struct_0('#skF_5')) | ~r2_hidden(A_212, a_2_1_orders_2('#skF_5', C_214)) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_146, c_1904])).
% 7.26/2.65  tff(c_1909, plain, (![A_212, C_214]: (m1_subset_1('#skF_3'(A_212, '#skF_5', C_214), k2_struct_0('#skF_5')) | ~r2_hidden(A_212, a_2_1_orders_2('#skF_5', C_214)) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_1908])).
% 7.26/2.65  tff(c_869, plain, (m1_subset_1('#skF_2'(k2_struct_0('#skF_5')), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_341])).
% 7.26/2.65  tff(c_20, plain, (![B_10, A_9]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, A_9) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.26/2.65  tff(c_874, plain, (v1_xboole_0('#skF_2'(k2_struct_0('#skF_5'))) | ~v1_xboole_0(k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_869, c_20])).
% 7.26/2.65  tff(c_875, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_874])).
% 7.26/2.65  tff(c_16, plain, (![B_10, A_9]: (r2_hidden(B_10, A_9) | ~m1_subset_1(B_10, A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.26/2.65  tff(c_2576, plain, (![B_242, A_243, C_244, E_245]: (r2_orders_2(B_242, '#skF_3'(A_243, B_242, C_244), E_245) | ~r2_hidden(E_245, C_244) | ~m1_subset_1(E_245, u1_struct_0(B_242)) | ~r2_hidden(A_243, a_2_1_orders_2(B_242, C_244)) | ~m1_subset_1(C_244, k1_zfmisc_1(u1_struct_0(B_242))) | ~l1_orders_2(B_242) | ~v5_orders_2(B_242) | ~v4_orders_2(B_242) | ~v3_orders_2(B_242) | v2_struct_0(B_242))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.26/2.65  tff(c_2597, plain, (![A_243, C_244, E_245]: (r2_orders_2('#skF_5', '#skF_3'(A_243, '#skF_5', C_244), E_245) | ~r2_hidden(E_245, C_244) | ~m1_subset_1(E_245, u1_struct_0('#skF_5')) | ~r2_hidden(A_243, a_2_1_orders_2('#skF_5', C_244)) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_2576])).
% 7.26/2.65  tff(c_2609, plain, (![A_243, C_244, E_245]: (r2_orders_2('#skF_5', '#skF_3'(A_243, '#skF_5', C_244), E_245) | ~r2_hidden(E_245, C_244) | ~m1_subset_1(E_245, k2_struct_0('#skF_5')) | ~r2_hidden(A_243, a_2_1_orders_2('#skF_5', C_244)) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_146, c_2597])).
% 7.26/2.65  tff(c_2751, plain, (![A_249, C_250, E_251]: (r2_orders_2('#skF_5', '#skF_3'(A_249, '#skF_5', C_250), E_251) | ~r2_hidden(E_251, C_250) | ~m1_subset_1(E_251, k2_struct_0('#skF_5')) | ~r2_hidden(A_249, a_2_1_orders_2('#skF_5', C_250)) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_70, c_2609])).
% 7.26/2.65  tff(c_4990, plain, (![A_352, E_353]: (r2_orders_2('#skF_5', '#skF_3'(A_352, '#skF_5', k2_struct_0('#skF_5')), E_353) | ~r2_hidden(E_353, k2_struct_0('#skF_5')) | ~m1_subset_1(E_353, k2_struct_0('#skF_5')) | ~r2_hidden(A_352, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_222, c_2751])).
% 7.26/2.65  tff(c_38, plain, (![A_42, C_48]: (~r2_orders_2(A_42, C_48, C_48) | ~m1_subset_1(C_48, u1_struct_0(A_42)) | ~l1_orders_2(A_42))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.26/2.65  tff(c_4998, plain, (![A_352]: (~m1_subset_1('#skF_3'(A_352, '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r2_hidden('#skF_3'(A_352, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_352, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_352, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_4990, c_38])).
% 7.26/2.65  tff(c_6155, plain, (![A_401]: (~r2_hidden('#skF_3'(A_401, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_401, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_401, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_146, c_4998])).
% 7.26/2.65  tff(c_6164, plain, (![A_401]: (~r2_hidden(A_401, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_3'(A_401, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | v1_xboole_0(k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_6155])).
% 7.26/2.65  tff(c_6172, plain, (![A_402]: (~r2_hidden(A_402, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_3'(A_402, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_875, c_6164])).
% 7.26/2.65  tff(c_6182, plain, (![A_212]: (~r2_hidden(A_212, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1909, c_6172])).
% 7.26/2.65  tff(c_6196, plain, (![A_403]: (~r2_hidden(A_403, a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_6182])).
% 7.26/2.65  tff(c_6204, plain, (a_2_1_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_6196])).
% 7.26/2.65  tff(c_6215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1082, c_6204])).
% 7.26/2.65  tff(c_6217, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_874])).
% 7.26/2.65  tff(c_119, plain, (![A_79]: (r2_hidden('#skF_2'(A_79), A_79) | k1_xboole_0=A_79)), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.26/2.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.26/2.65  tff(c_127, plain, (![A_79]: (~v1_xboole_0(A_79) | k1_xboole_0=A_79)), inference(resolution, [status(thm)], [c_119, c_2])).
% 7.26/2.65  tff(c_6220, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_6217, c_127])).
% 7.26/2.65  tff(c_6224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_870, c_6220])).
% 7.26/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/2.65  
% 7.26/2.65  Inference rules
% 7.26/2.65  ----------------------
% 7.26/2.65  #Ref     : 0
% 7.26/2.65  #Sup     : 1316
% 7.26/2.65  #Fact    : 0
% 7.26/2.66  #Define  : 0
% 7.26/2.66  #Split   : 21
% 7.26/2.66  #Chain   : 0
% 7.26/2.66  #Close   : 0
% 7.26/2.66  
% 7.26/2.66  Ordering : KBO
% 7.26/2.66  
% 7.26/2.66  Simplification rules
% 7.26/2.66  ----------------------
% 7.26/2.66  #Subsume      : 377
% 7.26/2.66  #Demod        : 1412
% 7.26/2.66  #Tautology    : 376
% 7.26/2.66  #SimpNegUnit  : 322
% 7.26/2.66  #BackRed      : 78
% 7.26/2.66  
% 7.26/2.66  #Partial instantiations: 0
% 7.26/2.66  #Strategies tried      : 1
% 7.26/2.66  
% 7.26/2.66  Timing (in seconds)
% 7.26/2.66  ----------------------
% 7.26/2.66  Preprocessing        : 0.46
% 7.26/2.66  Parsing              : 0.25
% 7.26/2.66  CNF conversion       : 0.03
% 7.26/2.66  Main loop            : 1.38
% 7.26/2.66  Inferencing          : 0.44
% 7.26/2.66  Reduction            : 0.47
% 7.26/2.66  Demodulation         : 0.33
% 7.26/2.66  BG Simplification    : 0.05
% 7.26/2.66  Subsumption          : 0.31
% 7.26/2.66  Abstraction          : 0.07
% 7.26/2.66  MUC search           : 0.00
% 7.26/2.66  Cooper               : 0.00
% 7.26/2.66  Total                : 1.88
% 7.26/2.66  Index Insertion      : 0.00
% 7.26/2.66  Index Deletion       : 0.00
% 7.26/2.66  Index Matching       : 0.00
% 7.26/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
