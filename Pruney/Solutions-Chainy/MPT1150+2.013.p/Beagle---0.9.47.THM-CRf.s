%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:25 EST 2020

% Result     : Theorem 52.73s
% Output     : CNFRefutation 52.81s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 412 expanded)
%              Number of leaves         :   40 ( 167 expanded)
%              Depth                    :   17
%              Number of atoms          :  224 (1106 expanded)
%              Number of equality atoms :   27 ( 188 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_93,axiom,(
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
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_139,axiom,(
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

tff(f_108,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_77,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_12,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_58,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_56,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_36,plain,(
    ! [A_28] :
      ( l1_struct_0(A_28)
      | ~ l1_orders_2(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    ! [A_46] :
      ( u1_struct_0(A_46) = k2_struct_0(A_46)
      | ~ l1_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    ! [A_47] :
      ( u1_struct_0(A_47) = k2_struct_0(A_47)
      | ~ l1_orders_2(A_47) ) ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_83,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_79])).

tff(c_586,plain,(
    ! [A_104,B_105] :
      ( k1_orders_2(A_104,B_105) = a_2_0_orders_2(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_613,plain,(
    ! [B_105] :
      ( k1_orders_2('#skF_5',B_105) = a_2_0_orders_2('#skF_5',B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_586])).

tff(c_629,plain,(
    ! [B_105] :
      ( k1_orders_2('#skF_5',B_105) = a_2_0_orders_2('#skF_5',B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_613])).

tff(c_633,plain,(
    ! [B_106] :
      ( k1_orders_2('#skF_5',B_106) = a_2_0_orders_2('#skF_5',B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_629])).

tff(c_672,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_61,c_633])).

tff(c_50,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_678,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_50])).

tff(c_153,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_70)
      | r2_hidden('#skF_2'(A_69,B_70),A_69)
      | B_70 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_89,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_95,plain,(
    ! [A_6,A_52] :
      ( ~ v1_xboole_0(A_6)
      | ~ r2_hidden(A_52,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_89])).

tff(c_101,plain,(
    ! [A_52] : ~ r2_hidden(A_52,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_182,plain,(
    ! [B_70] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_70),B_70)
      | k1_xboole_0 = B_70 ) ),
    inference(resolution,[status(thm)],[c_153,c_101])).

tff(c_1180,plain,(
    ! [A_128,B_129,C_130] :
      ( m1_subset_1('#skF_3'(A_128,B_129,C_130),u1_struct_0(B_129))
      | ~ r2_hidden(A_128,a_2_0_orders_2(B_129,C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0(B_129)))
      | ~ l1_orders_2(B_129)
      | ~ v5_orders_2(B_129)
      | ~ v4_orders_2(B_129)
      | ~ v3_orders_2(B_129)
      | v2_struct_0(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1185,plain,(
    ! [A_128,C_130] :
      ( m1_subset_1('#skF_3'(A_128,'#skF_5',C_130),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_128,a_2_0_orders_2('#skF_5',C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_1180])).

tff(c_1188,plain,(
    ! [A_128,C_130] :
      ( m1_subset_1('#skF_3'(A_128,'#skF_5',C_130),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_128,a_2_0_orders_2('#skF_5',C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_83,c_1185])).

tff(c_1189,plain,(
    ! [A_128,C_130] :
      ( m1_subset_1('#skF_3'(A_128,'#skF_5',C_130),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_128,a_2_0_orders_2('#skF_5',C_130))
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1188])).

tff(c_673,plain,(
    k1_orders_2('#skF_5',k1_xboole_0) = a_2_0_orders_2('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_633])).

tff(c_869,plain,(
    ! [A_115,B_116] :
      ( m1_subset_1(k1_orders_2(A_115,B_116),k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_orders_2(A_115)
      | ~ v5_orders_2(A_115)
      | ~ v4_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_882,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_869])).

tff(c_893,plain,
    ( m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_16,c_83,c_882])).

tff(c_894,plain,(
    m1_subset_1(a_2_0_orders_2('#skF_5',k1_xboole_0),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_893])).

tff(c_22,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_907,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_12,a_2_0_orders_2('#skF_5',k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_894,c_22])).

tff(c_918,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_907])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2483,plain,(
    ! [B_189,E_190,A_191,C_192] :
      ( r2_orders_2(B_189,E_190,'#skF_3'(A_191,B_189,C_192))
      | ~ r2_hidden(E_190,C_192)
      | ~ m1_subset_1(E_190,u1_struct_0(B_189))
      | ~ r2_hidden(A_191,a_2_0_orders_2(B_189,C_192))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(u1_struct_0(B_189)))
      | ~ l1_orders_2(B_189)
      | ~ v5_orders_2(B_189)
      | ~ v4_orders_2(B_189)
      | ~ v3_orders_2(B_189)
      | v2_struct_0(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_251972,plain,(
    ! [B_71418,E_71419,A_71420] :
      ( r2_orders_2(B_71418,E_71419,'#skF_3'(A_71420,B_71418,u1_struct_0(B_71418)))
      | ~ r2_hidden(E_71419,u1_struct_0(B_71418))
      | ~ m1_subset_1(E_71419,u1_struct_0(B_71418))
      | ~ r2_hidden(A_71420,a_2_0_orders_2(B_71418,u1_struct_0(B_71418)))
      | ~ l1_orders_2(B_71418)
      | ~ v5_orders_2(B_71418)
      | ~ v4_orders_2(B_71418)
      | ~ v3_orders_2(B_71418)
      | v2_struct_0(B_71418) ) ),
    inference(resolution,[status(thm)],[c_61,c_2483])).

tff(c_28,plain,(
    ! [A_16,C_22] :
      ( ~ r2_orders_2(A_16,C_22,C_22)
      | ~ m1_subset_1(C_22,u1_struct_0(A_16))
      | ~ l1_orders_2(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_455275,plain,(
    ! [A_129629,B_129630] :
      ( ~ r2_hidden('#skF_3'(A_129629,B_129630,u1_struct_0(B_129630)),u1_struct_0(B_129630))
      | ~ m1_subset_1('#skF_3'(A_129629,B_129630,u1_struct_0(B_129630)),u1_struct_0(B_129630))
      | ~ r2_hidden(A_129629,a_2_0_orders_2(B_129630,u1_struct_0(B_129630)))
      | ~ l1_orders_2(B_129630)
      | ~ v5_orders_2(B_129630)
      | ~ v4_orders_2(B_129630)
      | ~ v3_orders_2(B_129630)
      | v2_struct_0(B_129630) ) ),
    inference(resolution,[status(thm)],[c_251972,c_28])).

tff(c_455370,plain,(
    ! [A_129629] :
      ( ~ r2_hidden('#skF_3'(A_129629,'#skF_5',k2_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_129629,'#skF_5',u1_struct_0('#skF_5')),u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_129629,a_2_0_orders_2('#skF_5',u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_455275])).

tff(c_455380,plain,(
    ! [A_129629] :
      ( ~ r2_hidden('#skF_3'(A_129629,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_129629,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_129629,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_52,c_83,c_83,c_83,c_83,c_455370])).

tff(c_455385,plain,(
    ! [A_129802] :
      ( ~ r2_hidden('#skF_3'(A_129802,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_129802,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
      | ~ r2_hidden(A_129802,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_455380])).

tff(c_455462,plain,(
    ! [A_129802] :
      ( ~ r2_hidden(A_129802,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | v1_xboole_0(k2_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_3'(A_129802,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_18,c_455385])).

tff(c_455476,plain,(
    ! [A_129974] :
      ( ~ r2_hidden(A_129974,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_3'(A_129974,'#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_918,c_455462])).

tff(c_455554,plain,(
    ! [A_128] :
      ( ~ r2_hidden(A_128,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_1189,c_455476])).

tff(c_455570,plain,(
    ! [A_130146] : ~ r2_hidden(A_130146,a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_455554])).

tff(c_455675,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_455570])).

tff(c_455718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_678,c_455675])).

tff(c_455720,plain,(
    v1_xboole_0(k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_184,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_71),B_71)
      | k1_xboole_0 = B_71 ) ),
    inference(resolution,[status(thm)],[c_153,c_101])).

tff(c_94,plain,(
    ! [A_5,A_52] :
      ( ~ v1_xboole_0(A_5)
      | ~ r2_hidden(A_52,A_5) ) ),
    inference(resolution,[status(thm)],[c_61,c_89])).

tff(c_202,plain,(
    ! [B_71] :
      ( ~ v1_xboole_0(B_71)
      | k1_xboole_0 = B_71 ) ),
    inference(resolution,[status(thm)],[c_184,c_94])).

tff(c_455727,plain,(
    k2_struct_0('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_455720,c_202])).

tff(c_455731,plain,(
    a_2_0_orders_2('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_455727,c_678])).

tff(c_455799,plain,(
    ! [A_130321] : ~ r2_hidden(A_130321,a_2_0_orders_2('#skF_5',k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_907])).

tff(c_455819,plain,(
    a_2_0_orders_2('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_455799])).

tff(c_455843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_455731,c_455819])).

tff(c_455844,plain,(
    ! [A_6] : ~ v1_xboole_0(A_6) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_455847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_455844,c_2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:36:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.73/39.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.73/39.18  
% 52.73/39.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.73/39.18  %$ r2_orders_2 > r1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 52.73/39.18  
% 52.73/39.18  %Foreground sorts:
% 52.73/39.18  
% 52.73/39.18  
% 52.73/39.18  %Background operators:
% 52.73/39.18  
% 52.73/39.18  
% 52.73/39.18  %Foreground operators:
% 52.73/39.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 52.73/39.18  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 52.73/39.18  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 52.73/39.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.73/39.18  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 52.73/39.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 52.73/39.18  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 52.73/39.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 52.73/39.18  tff('#skF_5', type, '#skF_5': $i).
% 52.73/39.18  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 52.73/39.18  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 52.73/39.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 52.73/39.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 52.73/39.18  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 52.73/39.18  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 52.73/39.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.73/39.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 52.73/39.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.73/39.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 52.73/39.18  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 52.73/39.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 52.73/39.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 52.73/39.18  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 52.73/39.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 52.73/39.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 52.73/39.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 52.73/39.18  
% 52.81/39.20  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 52.81/39.20  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 52.81/39.20  tff(f_153, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 52.81/39.20  tff(f_112, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 52.81/39.20  tff(f_62, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 52.81/39.20  tff(f_93, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 52.81/39.20  tff(f_33, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 52.81/39.20  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 52.81/39.20  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 52.81/39.20  tff(f_139, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 52.81/39.20  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 52.81/39.20  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 52.81/39.20  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 52.81/39.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 52.81/39.20  tff(c_12, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_35])).
% 52.81/39.20  tff(c_14, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 52.81/39.20  tff(c_61, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 52.81/39.20  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 52.81/39.20  tff(c_58, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 52.81/39.20  tff(c_56, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 52.81/39.20  tff(c_54, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 52.81/39.20  tff(c_52, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 52.81/39.20  tff(c_36, plain, (![A_28]: (l1_struct_0(A_28) | ~l1_orders_2(A_28))), inference(cnfTransformation, [status(thm)], [f_112])).
% 52.81/39.20  tff(c_74, plain, (![A_46]: (u1_struct_0(A_46)=k2_struct_0(A_46) | ~l1_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 52.81/39.20  tff(c_79, plain, (![A_47]: (u1_struct_0(A_47)=k2_struct_0(A_47) | ~l1_orders_2(A_47))), inference(resolution, [status(thm)], [c_36, c_74])).
% 52.81/39.20  tff(c_83, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_79])).
% 52.81/39.20  tff(c_586, plain, (![A_104, B_105]: (k1_orders_2(A_104, B_105)=a_2_0_orders_2(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_93])).
% 52.81/39.20  tff(c_613, plain, (![B_105]: (k1_orders_2('#skF_5', B_105)=a_2_0_orders_2('#skF_5', B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_586])).
% 52.81/39.20  tff(c_629, plain, (![B_105]: (k1_orders_2('#skF_5', B_105)=a_2_0_orders_2('#skF_5', B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_613])).
% 52.81/39.20  tff(c_633, plain, (![B_106]: (k1_orders_2('#skF_5', B_106)=a_2_0_orders_2('#skF_5', B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_629])).
% 52.81/39.20  tff(c_672, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_61, c_633])).
% 52.81/39.20  tff(c_50, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_153])).
% 52.81/39.20  tff(c_678, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_672, c_50])).
% 52.81/39.20  tff(c_153, plain, (![A_69, B_70]: (r2_hidden('#skF_1'(A_69, B_70), B_70) | r2_hidden('#skF_2'(A_69, B_70), A_69) | B_70=A_69)), inference(cnfTransformation, [status(thm)], [f_33])).
% 52.81/39.20  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 52.81/39.20  tff(c_89, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_58])).
% 52.81/39.20  tff(c_95, plain, (![A_6, A_52]: (~v1_xboole_0(A_6) | ~r2_hidden(A_52, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_89])).
% 52.81/39.20  tff(c_101, plain, (![A_52]: (~r2_hidden(A_52, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_95])).
% 52.81/39.20  tff(c_182, plain, (![B_70]: (r2_hidden('#skF_1'(k1_xboole_0, B_70), B_70) | k1_xboole_0=B_70)), inference(resolution, [status(thm)], [c_153, c_101])).
% 52.81/39.20  tff(c_1180, plain, (![A_128, B_129, C_130]: (m1_subset_1('#skF_3'(A_128, B_129, C_130), u1_struct_0(B_129)) | ~r2_hidden(A_128, a_2_0_orders_2(B_129, C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0(B_129))) | ~l1_orders_2(B_129) | ~v5_orders_2(B_129) | ~v4_orders_2(B_129) | ~v3_orders_2(B_129) | v2_struct_0(B_129))), inference(cnfTransformation, [status(thm)], [f_139])).
% 52.81/39.20  tff(c_1185, plain, (![A_128, C_130]: (m1_subset_1('#skF_3'(A_128, '#skF_5', C_130), k2_struct_0('#skF_5')) | ~r2_hidden(A_128, a_2_0_orders_2('#skF_5', C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_1180])).
% 52.81/39.20  tff(c_1188, plain, (![A_128, C_130]: (m1_subset_1('#skF_3'(A_128, '#skF_5', C_130), k2_struct_0('#skF_5')) | ~r2_hidden(A_128, a_2_0_orders_2('#skF_5', C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_83, c_1185])).
% 52.81/39.20  tff(c_1189, plain, (![A_128, C_130]: (m1_subset_1('#skF_3'(A_128, '#skF_5', C_130), k2_struct_0('#skF_5')) | ~r2_hidden(A_128, a_2_0_orders_2('#skF_5', C_130)) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1188])).
% 52.81/39.20  tff(c_673, plain, (k1_orders_2('#skF_5', k1_xboole_0)=a_2_0_orders_2('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_633])).
% 52.81/39.20  tff(c_869, plain, (![A_115, B_116]: (m1_subset_1(k1_orders_2(A_115, B_116), k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_orders_2(A_115) | ~v5_orders_2(A_115) | ~v4_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_108])).
% 52.81/39.20  tff(c_882, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_673, c_869])).
% 52.81/39.20  tff(c_893, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_16, c_83, c_882])).
% 52.81/39.20  tff(c_894, plain, (m1_subset_1(a_2_0_orders_2('#skF_5', k1_xboole_0), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_893])).
% 52.81/39.20  tff(c_22, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_58])).
% 52.81/39.20  tff(c_907, plain, (![A_12]: (~v1_xboole_0(k2_struct_0('#skF_5')) | ~r2_hidden(A_12, a_2_0_orders_2('#skF_5', k1_xboole_0)))), inference(resolution, [status(thm)], [c_894, c_22])).
% 52.81/39.20  tff(c_918, plain, (~v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_907])).
% 52.81/39.20  tff(c_18, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 52.81/39.20  tff(c_2483, plain, (![B_189, E_190, A_191, C_192]: (r2_orders_2(B_189, E_190, '#skF_3'(A_191, B_189, C_192)) | ~r2_hidden(E_190, C_192) | ~m1_subset_1(E_190, u1_struct_0(B_189)) | ~r2_hidden(A_191, a_2_0_orders_2(B_189, C_192)) | ~m1_subset_1(C_192, k1_zfmisc_1(u1_struct_0(B_189))) | ~l1_orders_2(B_189) | ~v5_orders_2(B_189) | ~v4_orders_2(B_189) | ~v3_orders_2(B_189) | v2_struct_0(B_189))), inference(cnfTransformation, [status(thm)], [f_139])).
% 52.81/39.20  tff(c_251972, plain, (![B_71418, E_71419, A_71420]: (r2_orders_2(B_71418, E_71419, '#skF_3'(A_71420, B_71418, u1_struct_0(B_71418))) | ~r2_hidden(E_71419, u1_struct_0(B_71418)) | ~m1_subset_1(E_71419, u1_struct_0(B_71418)) | ~r2_hidden(A_71420, a_2_0_orders_2(B_71418, u1_struct_0(B_71418))) | ~l1_orders_2(B_71418) | ~v5_orders_2(B_71418) | ~v4_orders_2(B_71418) | ~v3_orders_2(B_71418) | v2_struct_0(B_71418))), inference(resolution, [status(thm)], [c_61, c_2483])).
% 52.81/39.20  tff(c_28, plain, (![A_16, C_22]: (~r2_orders_2(A_16, C_22, C_22) | ~m1_subset_1(C_22, u1_struct_0(A_16)) | ~l1_orders_2(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 52.81/39.20  tff(c_455275, plain, (![A_129629, B_129630]: (~r2_hidden('#skF_3'(A_129629, B_129630, u1_struct_0(B_129630)), u1_struct_0(B_129630)) | ~m1_subset_1('#skF_3'(A_129629, B_129630, u1_struct_0(B_129630)), u1_struct_0(B_129630)) | ~r2_hidden(A_129629, a_2_0_orders_2(B_129630, u1_struct_0(B_129630))) | ~l1_orders_2(B_129630) | ~v5_orders_2(B_129630) | ~v4_orders_2(B_129630) | ~v3_orders_2(B_129630) | v2_struct_0(B_129630))), inference(resolution, [status(thm)], [c_251972, c_28])).
% 52.81/39.20  tff(c_455370, plain, (![A_129629]: (~r2_hidden('#skF_3'(A_129629, '#skF_5', k2_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_129629, '#skF_5', u1_struct_0('#skF_5')), u1_struct_0('#skF_5')) | ~r2_hidden(A_129629, a_2_0_orders_2('#skF_5', u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_455275])).
% 52.81/39.20  tff(c_455380, plain, (![A_129629]: (~r2_hidden('#skF_3'(A_129629, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_129629, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_129629, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_52, c_83, c_83, c_83, c_83, c_455370])).
% 52.81/39.20  tff(c_455385, plain, (![A_129802]: (~r2_hidden('#skF_3'(A_129802, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_129802, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~r2_hidden(A_129802, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_455380])).
% 52.81/39.20  tff(c_455462, plain, (![A_129802]: (~r2_hidden(A_129802, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v1_xboole_0(k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_3'(A_129802, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_18, c_455385])).
% 52.81/39.20  tff(c_455476, plain, (![A_129974]: (~r2_hidden(A_129974, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_3'(A_129974, '#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_918, c_455462])).
% 52.81/39.20  tff(c_455554, plain, (![A_128]: (~r2_hidden(A_128, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_1189, c_455476])).
% 52.81/39.20  tff(c_455570, plain, (![A_130146]: (~r2_hidden(A_130146, a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_455554])).
% 52.81/39.20  tff(c_455675, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_455570])).
% 52.81/39.20  tff(c_455718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_678, c_455675])).
% 52.81/39.20  tff(c_455720, plain, (v1_xboole_0(k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_907])).
% 52.81/39.20  tff(c_184, plain, (![B_71]: (r2_hidden('#skF_1'(k1_xboole_0, B_71), B_71) | k1_xboole_0=B_71)), inference(resolution, [status(thm)], [c_153, c_101])).
% 52.81/39.20  tff(c_94, plain, (![A_5, A_52]: (~v1_xboole_0(A_5) | ~r2_hidden(A_52, A_5))), inference(resolution, [status(thm)], [c_61, c_89])).
% 52.81/39.20  tff(c_202, plain, (![B_71]: (~v1_xboole_0(B_71) | k1_xboole_0=B_71)), inference(resolution, [status(thm)], [c_184, c_94])).
% 52.81/39.20  tff(c_455727, plain, (k2_struct_0('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_455720, c_202])).
% 52.81/39.20  tff(c_455731, plain, (a_2_0_orders_2('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_455727, c_678])).
% 52.81/39.20  tff(c_455799, plain, (![A_130321]: (~r2_hidden(A_130321, a_2_0_orders_2('#skF_5', k1_xboole_0)))), inference(splitRight, [status(thm)], [c_907])).
% 52.81/39.20  tff(c_455819, plain, (a_2_0_orders_2('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_455799])).
% 52.81/39.20  tff(c_455843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_455731, c_455819])).
% 52.81/39.20  tff(c_455844, plain, (![A_6]: (~v1_xboole_0(A_6))), inference(splitRight, [status(thm)], [c_95])).
% 52.81/39.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 52.81/39.20  tff(c_455847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_455844, c_2])).
% 52.81/39.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.81/39.20  
% 52.81/39.20  Inference rules
% 52.81/39.20  ----------------------
% 52.81/39.20  #Ref     : 0
% 52.81/39.20  #Sup     : 54101
% 52.81/39.20  #Fact    : 18
% 52.81/39.20  #Define  : 0
% 52.81/39.20  #Split   : 41
% 52.81/39.20  #Chain   : 0
% 52.81/39.20  #Close   : 0
% 52.81/39.20  
% 52.81/39.20  Ordering : KBO
% 52.81/39.20  
% 52.81/39.20  Simplification rules
% 52.81/39.20  ----------------------
% 52.81/39.20  #Subsume      : 15377
% 52.81/39.20  #Demod        : 24564
% 52.81/39.20  #Tautology    : 6612
% 52.81/39.20  #SimpNegUnit  : 3872
% 52.81/39.20  #BackRed      : 317
% 52.81/39.20  
% 52.81/39.20  #Partial instantiations: 81708
% 52.81/39.20  #Strategies tried      : 1
% 52.81/39.20  
% 52.81/39.20  Timing (in seconds)
% 52.81/39.20  ----------------------
% 52.81/39.20  Preprocessing        : 0.35
% 52.81/39.20  Parsing              : 0.18
% 52.81/39.20  CNF conversion       : 0.03
% 52.81/39.20  Main loop            : 38.08
% 52.81/39.20  Inferencing          : 5.41
% 52.81/39.20  Reduction            : 10.14
% 52.81/39.20  Demodulation         : 7.20
% 52.81/39.20  BG Simplification    : 0.72
% 52.81/39.20  Subsumption          : 20.12
% 52.81/39.20  Abstraction          : 1.04
% 52.81/39.20  MUC search           : 0.00
% 52.81/39.20  Cooper               : 0.00
% 52.81/39.20  Total                : 38.47
% 52.81/39.20  Index Insertion      : 0.00
% 52.81/39.20  Index Deletion       : 0.00
% 52.81/39.20  Index Matching       : 0.00
% 52.81/39.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
