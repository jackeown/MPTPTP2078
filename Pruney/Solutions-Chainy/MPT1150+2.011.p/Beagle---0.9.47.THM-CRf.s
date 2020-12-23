%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:25 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 15.52s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 534 expanded)
%              Number of leaves         :   34 ( 211 expanded)
%              Depth                    :   21
%              Number of atoms          :  370 (1618 expanded)
%              Number of equality atoms :   24 ( 220 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_94,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_75,axiom,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_121,axiom,(
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

tff(f_59,axiom,(
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

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden('#skF_1'(A_46,B_47),B_47)
      | r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_48,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_46,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_44,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_42,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_26,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_orders_2(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_53,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = k2_struct_0(A_38)
      | ~ l1_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    ! [A_41] :
      ( u1_struct_0(A_41) = k2_struct_0(A_41)
      | ~ l1_orders_2(A_41) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_63,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_112,plain,(
    ! [A_69,B_70] :
      ( k1_orders_2(A_69,B_70) = a_2_0_orders_2(A_69,B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_orders_2(A_69)
      | ~ v5_orders_2(A_69)
      | ~ v4_orders_2(A_69)
      | ~ v3_orders_2(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_115,plain,(
    ! [B_70] :
      ( k1_orders_2('#skF_4',B_70) = a_2_0_orders_2('#skF_4',B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_112])).

tff(c_121,plain,(
    ! [B_70] :
      ( k1_orders_2('#skF_4',B_70) = a_2_0_orders_2('#skF_4',B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_115])).

tff(c_124,plain,(
    ! [B_71] :
      ( k1_orders_2('#skF_4',B_71) = a_2_0_orders_2('#skF_4',B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_121])).

tff(c_145,plain,(
    ! [A_74] :
      ( k1_orders_2('#skF_4',A_74) = a_2_0_orders_2('#skF_4',A_74)
      | ~ r1_tarski(A_74,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_124])).

tff(c_150,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) = a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_79,c_145])).

tff(c_40,plain,(
    k1_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_151,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_40])).

tff(c_130,plain,(
    ! [A_72,B_73] :
      ( m1_subset_1(k1_orders_2(A_72,B_73),k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_139,plain,(
    ! [B_73] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_73),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_130])).

tff(c_143,plain,(
    ! [B_73] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_73),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_139])).

tff(c_162,plain,(
    ! [B_75] :
      ( m1_subset_1(k1_orders_2('#skF_4',B_75),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_143])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_174,plain,(
    ! [B_76] :
      ( r1_tarski(k1_orders_2('#skF_4',B_76),k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_162,c_10])).

tff(c_182,plain,
    ( r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),k2_struct_0('#skF_4'))
    | ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_174])).

tff(c_185,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_188,plain,(
    ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_12,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_188])).

tff(c_194,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_80,plain,(
    ! [C_48,B_49,A_50] :
      ( r2_hidden(C_48,B_49)
      | ~ r2_hidden(C_48,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_83,plain,(
    ! [A_1,B_2,B_49] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_49)
      | ~ r1_tarski(A_1,B_49)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_212,plain,(
    ! [A_77,B_78,C_79] :
      ( '#skF_2'(A_77,B_78,C_79) = A_77
      | ~ r2_hidden(A_77,a_2_0_orders_2(B_78,C_79))
      | ~ m1_subset_1(C_79,k1_zfmisc_1(u1_struct_0(B_78)))
      | ~ l1_orders_2(B_78)
      | ~ v5_orders_2(B_78)
      | ~ v4_orders_2(B_78)
      | ~ v3_orders_2(B_78)
      | v2_struct_0(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1807,plain,(
    ! [B_182,C_183,B_184] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_182,C_183),B_184),B_182,C_183) = '#skF_1'(a_2_0_orders_2(B_182,C_183),B_184)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(u1_struct_0(B_182)))
      | ~ l1_orders_2(B_182)
      | ~ v5_orders_2(B_182)
      | ~ v4_orders_2(B_182)
      | ~ v3_orders_2(B_182)
      | v2_struct_0(B_182)
      | r1_tarski(a_2_0_orders_2(B_182,C_183),B_184) ) ),
    inference(resolution,[status(thm)],[c_6,c_212])).

tff(c_4029,plain,(
    ! [B_275,A_276,B_277] :
      ( '#skF_2'('#skF_1'(a_2_0_orders_2(B_275,A_276),B_277),B_275,A_276) = '#skF_1'(a_2_0_orders_2(B_275,A_276),B_277)
      | ~ l1_orders_2(B_275)
      | ~ v5_orders_2(B_275)
      | ~ v4_orders_2(B_275)
      | ~ v3_orders_2(B_275)
      | v2_struct_0(B_275)
      | r1_tarski(a_2_0_orders_2(B_275,A_276),B_277)
      | ~ r1_tarski(A_276,u1_struct_0(B_275)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1807])).

tff(c_321,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_2'(A_84,B_85,C_86),u1_struct_0(B_85))
      | ~ r2_hidden(A_84,a_2_0_orders_2(B_85,C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0(B_85)))
      | ~ l1_orders_2(B_85)
      | ~ v5_orders_2(B_85)
      | ~ v4_orders_2(B_85)
      | ~ v3_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_326,plain,(
    ! [A_84,C_86] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4',C_86),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_84,a_2_0_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_321])).

tff(c_329,plain,(
    ! [A_84,C_86] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4',C_86),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_84,a_2_0_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_326])).

tff(c_330,plain,(
    ! [A_84,C_86] :
      ( m1_subset_1('#skF_2'(A_84,'#skF_4',C_86),k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_84,a_2_0_orders_2('#skF_4',C_86))
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_329])).

tff(c_4070,plain,(
    ! [A_276,B_277] :
      ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277),k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277),a_2_0_orders_2('#skF_4',A_276))
      | ~ m1_subset_1(A_276,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(a_2_0_orders_2('#skF_4',A_276),B_277)
      | ~ r1_tarski(A_276,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4029,c_330])).

tff(c_4108,plain,(
    ! [A_276,B_277] :
      ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277),k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277),a_2_0_orders_2('#skF_4',A_276))
      | ~ m1_subset_1(A_276,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | r1_tarski(a_2_0_orders_2('#skF_4',A_276),B_277)
      | ~ r1_tarski(A_276,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_44,c_42,c_4070])).

tff(c_4511,plain,(
    ! [A_292,B_293] :
      ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_292),B_293),k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_292),B_293),a_2_0_orders_2('#skF_4',A_292))
      | ~ m1_subset_1(A_292,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_292),B_293)
      | ~ r1_tarski(A_292,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4108])).

tff(c_4527,plain,(
    ! [A_292,B_2] :
      ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_292),B_2),k2_struct_0('#skF_4'))
      | ~ m1_subset_1(A_292,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r1_tarski(A_292,k2_struct_0('#skF_4'))
      | ~ r1_tarski(a_2_0_orders_2('#skF_4',A_292),a_2_0_orders_2('#skF_4',A_292))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_292),B_2) ) ),
    inference(resolution,[status(thm)],[c_83,c_4511])).

tff(c_4543,plain,(
    ! [A_292,B_2] :
      ( m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_292),B_2),k2_struct_0('#skF_4'))
      | ~ m1_subset_1(A_292,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r1_tarski(A_292,k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_292),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_4527])).

tff(c_660,plain,(
    ! [A_121,A_122] :
      ( k1_orders_2(A_121,A_122) = a_2_0_orders_2(A_121,A_122)
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121)
      | ~ r1_tarski(A_122,u1_struct_0(A_121)) ) ),
    inference(resolution,[status(thm)],[c_12,c_112])).

tff(c_673,plain,(
    ! [A_121] :
      ( k1_orders_2(A_121,u1_struct_0(A_121)) = a_2_0_orders_2(A_121,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v5_orders_2(A_121)
      | ~ v4_orders_2(A_121)
      | ~ v3_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_79,c_660])).

tff(c_848,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(k1_orders_2(A_135,B_136),u1_struct_0(A_135))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_orders_2(A_135)
      | ~ v5_orders_2(A_135)
      | ~ v4_orders_2(A_135)
      | ~ v3_orders_2(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_130,c_10])).

tff(c_12586,plain,(
    ! [A_470] :
      ( r1_tarski(a_2_0_orders_2(A_470,u1_struct_0(A_470)),u1_struct_0(A_470))
      | ~ m1_subset_1(u1_struct_0(A_470),k1_zfmisc_1(u1_struct_0(A_470)))
      | ~ l1_orders_2(A_470)
      | ~ v5_orders_2(A_470)
      | ~ v4_orders_2(A_470)
      | ~ v3_orders_2(A_470)
      | v2_struct_0(A_470)
      | ~ l1_orders_2(A_470)
      | ~ v5_orders_2(A_470)
      | ~ v4_orders_2(A_470)
      | ~ v3_orders_2(A_470)
      | v2_struct_0(A_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_673,c_848])).

tff(c_92,plain,(
    ! [A_54,B_55,B_56] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_56)
      | ~ r1_tarski(A_54,B_56)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_54,B_55,B_2,B_56] :
      ( r2_hidden('#skF_1'(A_54,B_55),B_2)
      | ~ r1_tarski(B_56,B_2)
      | ~ r1_tarski(A_54,B_56)
      | r1_tarski(A_54,B_55) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_17124,plain,(
    ! [A_516,B_517,A_518] :
      ( r2_hidden('#skF_1'(A_516,B_517),u1_struct_0(A_518))
      | ~ r1_tarski(A_516,a_2_0_orders_2(A_518,u1_struct_0(A_518)))
      | r1_tarski(A_516,B_517)
      | ~ m1_subset_1(u1_struct_0(A_518),k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ l1_orders_2(A_518)
      | ~ v5_orders_2(A_518)
      | ~ v4_orders_2(A_518)
      | ~ v3_orders_2(A_518)
      | v2_struct_0(A_518) ) ),
    inference(resolution,[status(thm)],[c_12586,c_99])).

tff(c_17210,plain,(
    ! [A_518,B_517] :
      ( r2_hidden('#skF_1'(a_2_0_orders_2(A_518,u1_struct_0(A_518)),B_517),u1_struct_0(A_518))
      | r1_tarski(a_2_0_orders_2(A_518,u1_struct_0(A_518)),B_517)
      | ~ m1_subset_1(u1_struct_0(A_518),k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ l1_orders_2(A_518)
      | ~ v5_orders_2(A_518)
      | ~ v4_orders_2(A_518)
      | ~ v3_orders_2(A_518)
      | v2_struct_0(A_518) ) ),
    inference(resolution,[status(thm)],[c_79,c_17124])).

tff(c_807,plain,(
    ! [B_128,E_129,A_130,C_131] :
      ( r2_orders_2(B_128,E_129,'#skF_2'(A_130,B_128,C_131))
      | ~ r2_hidden(E_129,C_131)
      | ~ m1_subset_1(E_129,u1_struct_0(B_128))
      | ~ r2_hidden(A_130,a_2_0_orders_2(B_128,C_131))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(u1_struct_0(B_128)))
      | ~ l1_orders_2(B_128)
      | ~ v5_orders_2(B_128)
      | ~ v4_orders_2(B_128)
      | ~ v3_orders_2(B_128)
      | v2_struct_0(B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_811,plain,(
    ! [E_129,A_130,C_131] :
      ( r2_orders_2('#skF_4',E_129,'#skF_2'(A_130,'#skF_4',C_131))
      | ~ r2_hidden(E_129,C_131)
      | ~ m1_subset_1(E_129,u1_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',C_131))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_807])).

tff(c_817,plain,(
    ! [E_129,A_130,C_131] :
      ( r2_orders_2('#skF_4',E_129,'#skF_2'(A_130,'#skF_4',C_131))
      | ~ r2_hidden(E_129,C_131)
      | ~ m1_subset_1(E_129,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_130,a_2_0_orders_2('#skF_4',C_131))
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_811])).

tff(c_823,plain,(
    ! [E_132,A_133,C_134] :
      ( r2_orders_2('#skF_4',E_132,'#skF_2'(A_133,'#skF_4',C_134))
      | ~ r2_hidden(E_132,C_134)
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_133,a_2_0_orders_2('#skF_4',C_134))
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_817])).

tff(c_845,plain,(
    ! [E_132,A_133,A_7] :
      ( r2_orders_2('#skF_4',E_132,'#skF_2'(A_133,'#skF_4',A_7))
      | ~ r2_hidden(E_132,A_7)
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden(A_133,a_2_0_orders_2('#skF_4',A_7))
      | ~ r1_tarski(A_7,k2_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12,c_823])).

tff(c_4047,plain,(
    ! [E_132,A_276,B_277] :
      ( r2_orders_2('#skF_4',E_132,'#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277))
      | ~ r2_hidden(E_132,A_276)
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277),a_2_0_orders_2('#skF_4',A_276))
      | ~ r1_tarski(A_276,k2_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | r1_tarski(a_2_0_orders_2('#skF_4',A_276),B_277)
      | ~ r1_tarski(A_276,u1_struct_0('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4029,c_845])).

tff(c_4091,plain,(
    ! [E_132,A_276,B_277] :
      ( r2_orders_2('#skF_4',E_132,'#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277))
      | ~ r2_hidden(E_132,A_276)
      | ~ m1_subset_1(E_132,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_276),B_277),a_2_0_orders_2('#skF_4',A_276))
      | v2_struct_0('#skF_4')
      | r1_tarski(a_2_0_orders_2('#skF_4',A_276),B_277)
      | ~ r1_tarski(A_276,k2_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_44,c_42,c_4047])).

tff(c_26343,plain,(
    ! [E_640,A_641,B_642] :
      ( r2_orders_2('#skF_4',E_640,'#skF_1'(a_2_0_orders_2('#skF_4',A_641),B_642))
      | ~ r2_hidden(E_640,A_641)
      | ~ m1_subset_1(E_640,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_641),B_642),a_2_0_orders_2('#skF_4',A_641))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_641),B_642)
      | ~ r1_tarski(A_641,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_4091])).

tff(c_26371,plain,(
    ! [E_640,A_641,B_2] :
      ( r2_orders_2('#skF_4',E_640,'#skF_1'(a_2_0_orders_2('#skF_4',A_641),B_2))
      | ~ r2_hidden(E_640,A_641)
      | ~ m1_subset_1(E_640,k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_641,k2_struct_0('#skF_4'))
      | ~ r1_tarski(a_2_0_orders_2('#skF_4',A_641),a_2_0_orders_2('#skF_4',A_641))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_641),B_2) ) ),
    inference(resolution,[status(thm)],[c_83,c_26343])).

tff(c_26405,plain,(
    ! [E_643,A_644,B_645] :
      ( r2_orders_2('#skF_4',E_643,'#skF_1'(a_2_0_orders_2('#skF_4',A_644),B_645))
      | ~ r2_hidden(E_643,A_644)
      | ~ m1_subset_1(E_643,k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_644,k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_644),B_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_26371])).

tff(c_18,plain,(
    ! [A_10,C_16] :
      ( ~ r2_orders_2(A_10,C_16,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26413,plain,(
    ! [A_644,B_645] :
      ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_644),B_645),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_644),B_645),A_644)
      | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_644),B_645),k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_644,k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_644),B_645) ) ),
    inference(resolution,[status(thm)],[c_26405,c_18])).

tff(c_26431,plain,(
    ! [A_646,B_647] :
      ( ~ r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4',A_646),B_647),A_646)
      | ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',A_646),B_647),k2_struct_0('#skF_4'))
      | ~ r1_tarski(A_646,k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',A_646),B_647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63,c_26413])).

tff(c_26440,plain,(
    ! [B_517] :
      ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')),B_517),k2_struct_0('#skF_4'))
      | ~ r1_tarski(u1_struct_0('#skF_4'),k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',u1_struct_0('#skF_4')),B_517)
      | ~ m1_subset_1(u1_struct_0('#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_17210,c_26431])).

tff(c_26474,plain,(
    ! [B_517] :
      ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),B_517),k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),B_517)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_194,c_63,c_63,c_63,c_79,c_63,c_63,c_26440])).

tff(c_26499,plain,(
    ! [B_648] :
      ( ~ m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),B_648),k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),B_648) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_26474])).

tff(c_26503,plain,(
    ! [B_2] :
      ( ~ m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
      | r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),B_2) ) ),
    inference(resolution,[status(thm)],[c_4543,c_26499])).

tff(c_26524,plain,(
    ! [B_649] : r1_tarski(a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')),B_649) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_194,c_26503])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_26687,plain,(
    a_2_0_orders_2('#skF_4',k2_struct_0('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26524,c_8])).

tff(c_26793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_26687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.41/6.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.49/6.77  
% 15.49/6.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.52/6.77  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 15.52/6.77  
% 15.52/6.77  %Foreground sorts:
% 15.52/6.77  
% 15.52/6.77  
% 15.52/6.77  %Background operators:
% 15.52/6.77  
% 15.52/6.77  
% 15.52/6.77  %Foreground operators:
% 15.52/6.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.52/6.77  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 15.52/6.77  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 15.52/6.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.52/6.77  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 15.52/6.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.52/6.77  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 15.52/6.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.52/6.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.52/6.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.52/6.77  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 15.52/6.77  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 15.52/6.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.52/6.77  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.52/6.77  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 15.52/6.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.52/6.77  tff('#skF_4', type, '#skF_4': $i).
% 15.52/6.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.52/6.77  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 15.52/6.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 15.52/6.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.52/6.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.52/6.77  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 15.52/6.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.52/6.77  
% 15.52/6.79  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.52/6.79  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 15.52/6.79  tff(f_135, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 15.52/6.79  tff(f_94, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 15.52/6.79  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 15.52/6.79  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 15.52/6.79  tff(f_90, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 15.52/6.79  tff(f_121, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 15.52/6.79  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 15.52/6.79  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 15.52/6.79  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.52/6.79  tff(c_74, plain, (![A_46, B_47]: (~r2_hidden('#skF_1'(A_46, B_47), B_47) | r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.52/6.79  tff(c_79, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_74])).
% 15.52/6.79  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.52/6.79  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.52/6.79  tff(c_48, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.52/6.79  tff(c_46, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.52/6.79  tff(c_44, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.52/6.79  tff(c_42, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.52/6.79  tff(c_26, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_orders_2(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.52/6.79  tff(c_53, plain, (![A_38]: (u1_struct_0(A_38)=k2_struct_0(A_38) | ~l1_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.52/6.79  tff(c_59, plain, (![A_41]: (u1_struct_0(A_41)=k2_struct_0(A_41) | ~l1_orders_2(A_41))), inference(resolution, [status(thm)], [c_26, c_53])).
% 15.52/6.79  tff(c_63, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 15.52/6.79  tff(c_112, plain, (![A_69, B_70]: (k1_orders_2(A_69, B_70)=a_2_0_orders_2(A_69, B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_orders_2(A_69) | ~v5_orders_2(A_69) | ~v4_orders_2(A_69) | ~v3_orders_2(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.52/6.79  tff(c_115, plain, (![B_70]: (k1_orders_2('#skF_4', B_70)=a_2_0_orders_2('#skF_4', B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_112])).
% 15.52/6.79  tff(c_121, plain, (![B_70]: (k1_orders_2('#skF_4', B_70)=a_2_0_orders_2('#skF_4', B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_115])).
% 15.52/6.79  tff(c_124, plain, (![B_71]: (k1_orders_2('#skF_4', B_71)=a_2_0_orders_2('#skF_4', B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_121])).
% 15.52/6.79  tff(c_145, plain, (![A_74]: (k1_orders_2('#skF_4', A_74)=a_2_0_orders_2('#skF_4', A_74) | ~r1_tarski(A_74, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_124])).
% 15.52/6.79  tff(c_150, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))=a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_79, c_145])).
% 15.52/6.79  tff(c_40, plain, (k1_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_135])).
% 15.52/6.79  tff(c_151, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_40])).
% 15.52/6.79  tff(c_130, plain, (![A_72, B_73]: (m1_subset_1(k1_orders_2(A_72, B_73), k1_zfmisc_1(u1_struct_0(A_72))) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_90])).
% 15.52/6.79  tff(c_139, plain, (![B_73]: (m1_subset_1(k1_orders_2('#skF_4', B_73), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_130])).
% 15.52/6.79  tff(c_143, plain, (![B_73]: (m1_subset_1(k1_orders_2('#skF_4', B_73), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_73, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_139])).
% 15.52/6.79  tff(c_162, plain, (![B_75]: (m1_subset_1(k1_orders_2('#skF_4', B_75), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_subset_1(B_75, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_143])).
% 15.52/6.79  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.52/6.79  tff(c_174, plain, (![B_76]: (r1_tarski(k1_orders_2('#skF_4', B_76), k2_struct_0('#skF_4')) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_162, c_10])).
% 15.52/6.79  tff(c_182, plain, (r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), k2_struct_0('#skF_4')) | ~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_150, c_174])).
% 15.52/6.79  tff(c_185, plain, (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_182])).
% 15.52/6.79  tff(c_188, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_12, c_185])).
% 15.52/6.79  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_188])).
% 15.52/6.79  tff(c_194, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_182])).
% 15.52/6.79  tff(c_80, plain, (![C_48, B_49, A_50]: (r2_hidden(C_48, B_49) | ~r2_hidden(C_48, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.52/6.79  tff(c_83, plain, (![A_1, B_2, B_49]: (r2_hidden('#skF_1'(A_1, B_2), B_49) | ~r1_tarski(A_1, B_49) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_80])).
% 15.52/6.79  tff(c_212, plain, (![A_77, B_78, C_79]: ('#skF_2'(A_77, B_78, C_79)=A_77 | ~r2_hidden(A_77, a_2_0_orders_2(B_78, C_79)) | ~m1_subset_1(C_79, k1_zfmisc_1(u1_struct_0(B_78))) | ~l1_orders_2(B_78) | ~v5_orders_2(B_78) | ~v4_orders_2(B_78) | ~v3_orders_2(B_78) | v2_struct_0(B_78))), inference(cnfTransformation, [status(thm)], [f_121])).
% 15.52/6.79  tff(c_1807, plain, (![B_182, C_183, B_184]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_182, C_183), B_184), B_182, C_183)='#skF_1'(a_2_0_orders_2(B_182, C_183), B_184) | ~m1_subset_1(C_183, k1_zfmisc_1(u1_struct_0(B_182))) | ~l1_orders_2(B_182) | ~v5_orders_2(B_182) | ~v4_orders_2(B_182) | ~v3_orders_2(B_182) | v2_struct_0(B_182) | r1_tarski(a_2_0_orders_2(B_182, C_183), B_184))), inference(resolution, [status(thm)], [c_6, c_212])).
% 15.52/6.79  tff(c_4029, plain, (![B_275, A_276, B_277]: ('#skF_2'('#skF_1'(a_2_0_orders_2(B_275, A_276), B_277), B_275, A_276)='#skF_1'(a_2_0_orders_2(B_275, A_276), B_277) | ~l1_orders_2(B_275) | ~v5_orders_2(B_275) | ~v4_orders_2(B_275) | ~v3_orders_2(B_275) | v2_struct_0(B_275) | r1_tarski(a_2_0_orders_2(B_275, A_276), B_277) | ~r1_tarski(A_276, u1_struct_0(B_275)))), inference(resolution, [status(thm)], [c_12, c_1807])).
% 15.52/6.79  tff(c_321, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_2'(A_84, B_85, C_86), u1_struct_0(B_85)) | ~r2_hidden(A_84, a_2_0_orders_2(B_85, C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0(B_85))) | ~l1_orders_2(B_85) | ~v5_orders_2(B_85) | ~v4_orders_2(B_85) | ~v3_orders_2(B_85) | v2_struct_0(B_85))), inference(cnfTransformation, [status(thm)], [f_121])).
% 15.52/6.79  tff(c_326, plain, (![A_84, C_86]: (m1_subset_1('#skF_2'(A_84, '#skF_4', C_86), k2_struct_0('#skF_4')) | ~r2_hidden(A_84, a_2_0_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_321])).
% 15.52/6.79  tff(c_329, plain, (![A_84, C_86]: (m1_subset_1('#skF_2'(A_84, '#skF_4', C_86), k2_struct_0('#skF_4')) | ~r2_hidden(A_84, a_2_0_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_326])).
% 15.52/6.79  tff(c_330, plain, (![A_84, C_86]: (m1_subset_1('#skF_2'(A_84, '#skF_4', C_86), k2_struct_0('#skF_4')) | ~r2_hidden(A_84, a_2_0_orders_2('#skF_4', C_86)) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_329])).
% 15.52/6.79  tff(c_4070, plain, (![A_276, B_277]: (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277), a_2_0_orders_2('#skF_4', A_276)) | ~m1_subset_1(A_276, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(a_2_0_orders_2('#skF_4', A_276), B_277) | ~r1_tarski(A_276, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4029, c_330])).
% 15.52/6.79  tff(c_4108, plain, (![A_276, B_277]: (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277), a_2_0_orders_2('#skF_4', A_276)) | ~m1_subset_1(A_276, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | r1_tarski(a_2_0_orders_2('#skF_4', A_276), B_277) | ~r1_tarski(A_276, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_44, c_42, c_4070])).
% 15.52/6.79  tff(c_4511, plain, (![A_292, B_293]: (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_292), B_293), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_292), B_293), a_2_0_orders_2('#skF_4', A_292)) | ~m1_subset_1(A_292, k1_zfmisc_1(k2_struct_0('#skF_4'))) | r1_tarski(a_2_0_orders_2('#skF_4', A_292), B_293) | ~r1_tarski(A_292, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_4108])).
% 15.52/6.79  tff(c_4527, plain, (![A_292, B_2]: (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_292), B_2), k2_struct_0('#skF_4')) | ~m1_subset_1(A_292, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~r1_tarski(A_292, k2_struct_0('#skF_4')) | ~r1_tarski(a_2_0_orders_2('#skF_4', A_292), a_2_0_orders_2('#skF_4', A_292)) | r1_tarski(a_2_0_orders_2('#skF_4', A_292), B_2))), inference(resolution, [status(thm)], [c_83, c_4511])).
% 15.52/6.79  tff(c_4543, plain, (![A_292, B_2]: (m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_292), B_2), k2_struct_0('#skF_4')) | ~m1_subset_1(A_292, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~r1_tarski(A_292, k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', A_292), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_4527])).
% 15.52/6.79  tff(c_660, plain, (![A_121, A_122]: (k1_orders_2(A_121, A_122)=a_2_0_orders_2(A_121, A_122) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121) | ~r1_tarski(A_122, u1_struct_0(A_121)))), inference(resolution, [status(thm)], [c_12, c_112])).
% 15.52/6.79  tff(c_673, plain, (![A_121]: (k1_orders_2(A_121, u1_struct_0(A_121))=a_2_0_orders_2(A_121, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v5_orders_2(A_121) | ~v4_orders_2(A_121) | ~v3_orders_2(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_79, c_660])).
% 15.52/6.79  tff(c_848, plain, (![A_135, B_136]: (r1_tarski(k1_orders_2(A_135, B_136), u1_struct_0(A_135)) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_orders_2(A_135) | ~v5_orders_2(A_135) | ~v4_orders_2(A_135) | ~v3_orders_2(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_130, c_10])).
% 15.52/6.79  tff(c_12586, plain, (![A_470]: (r1_tarski(a_2_0_orders_2(A_470, u1_struct_0(A_470)), u1_struct_0(A_470)) | ~m1_subset_1(u1_struct_0(A_470), k1_zfmisc_1(u1_struct_0(A_470))) | ~l1_orders_2(A_470) | ~v5_orders_2(A_470) | ~v4_orders_2(A_470) | ~v3_orders_2(A_470) | v2_struct_0(A_470) | ~l1_orders_2(A_470) | ~v5_orders_2(A_470) | ~v4_orders_2(A_470) | ~v3_orders_2(A_470) | v2_struct_0(A_470))), inference(superposition, [status(thm), theory('equality')], [c_673, c_848])).
% 15.52/6.79  tff(c_92, plain, (![A_54, B_55, B_56]: (r2_hidden('#skF_1'(A_54, B_55), B_56) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_6, c_80])).
% 15.52/6.79  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.52/6.79  tff(c_99, plain, (![A_54, B_55, B_2, B_56]: (r2_hidden('#skF_1'(A_54, B_55), B_2) | ~r1_tarski(B_56, B_2) | ~r1_tarski(A_54, B_56) | r1_tarski(A_54, B_55))), inference(resolution, [status(thm)], [c_92, c_2])).
% 15.52/6.79  tff(c_17124, plain, (![A_516, B_517, A_518]: (r2_hidden('#skF_1'(A_516, B_517), u1_struct_0(A_518)) | ~r1_tarski(A_516, a_2_0_orders_2(A_518, u1_struct_0(A_518))) | r1_tarski(A_516, B_517) | ~m1_subset_1(u1_struct_0(A_518), k1_zfmisc_1(u1_struct_0(A_518))) | ~l1_orders_2(A_518) | ~v5_orders_2(A_518) | ~v4_orders_2(A_518) | ~v3_orders_2(A_518) | v2_struct_0(A_518))), inference(resolution, [status(thm)], [c_12586, c_99])).
% 15.52/6.79  tff(c_17210, plain, (![A_518, B_517]: (r2_hidden('#skF_1'(a_2_0_orders_2(A_518, u1_struct_0(A_518)), B_517), u1_struct_0(A_518)) | r1_tarski(a_2_0_orders_2(A_518, u1_struct_0(A_518)), B_517) | ~m1_subset_1(u1_struct_0(A_518), k1_zfmisc_1(u1_struct_0(A_518))) | ~l1_orders_2(A_518) | ~v5_orders_2(A_518) | ~v4_orders_2(A_518) | ~v3_orders_2(A_518) | v2_struct_0(A_518))), inference(resolution, [status(thm)], [c_79, c_17124])).
% 15.52/6.79  tff(c_807, plain, (![B_128, E_129, A_130, C_131]: (r2_orders_2(B_128, E_129, '#skF_2'(A_130, B_128, C_131)) | ~r2_hidden(E_129, C_131) | ~m1_subset_1(E_129, u1_struct_0(B_128)) | ~r2_hidden(A_130, a_2_0_orders_2(B_128, C_131)) | ~m1_subset_1(C_131, k1_zfmisc_1(u1_struct_0(B_128))) | ~l1_orders_2(B_128) | ~v5_orders_2(B_128) | ~v4_orders_2(B_128) | ~v3_orders_2(B_128) | v2_struct_0(B_128))), inference(cnfTransformation, [status(thm)], [f_121])).
% 15.52/6.79  tff(c_811, plain, (![E_129, A_130, C_131]: (r2_orders_2('#skF_4', E_129, '#skF_2'(A_130, '#skF_4', C_131)) | ~r2_hidden(E_129, C_131) | ~m1_subset_1(E_129, u1_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_0_orders_2('#skF_4', C_131)) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_807])).
% 15.52/6.79  tff(c_817, plain, (![E_129, A_130, C_131]: (r2_orders_2('#skF_4', E_129, '#skF_2'(A_130, '#skF_4', C_131)) | ~r2_hidden(E_129, C_131) | ~m1_subset_1(E_129, k2_struct_0('#skF_4')) | ~r2_hidden(A_130, a_2_0_orders_2('#skF_4', C_131)) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_811])).
% 15.52/6.79  tff(c_823, plain, (![E_132, A_133, C_134]: (r2_orders_2('#skF_4', E_132, '#skF_2'(A_133, '#skF_4', C_134)) | ~r2_hidden(E_132, C_134) | ~m1_subset_1(E_132, k2_struct_0('#skF_4')) | ~r2_hidden(A_133, a_2_0_orders_2('#skF_4', C_134)) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_817])).
% 15.52/6.79  tff(c_845, plain, (![E_132, A_133, A_7]: (r2_orders_2('#skF_4', E_132, '#skF_2'(A_133, '#skF_4', A_7)) | ~r2_hidden(E_132, A_7) | ~m1_subset_1(E_132, k2_struct_0('#skF_4')) | ~r2_hidden(A_133, a_2_0_orders_2('#skF_4', A_7)) | ~r1_tarski(A_7, k2_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12, c_823])).
% 15.52/6.79  tff(c_4047, plain, (![E_132, A_276, B_277]: (r2_orders_2('#skF_4', E_132, '#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277)) | ~r2_hidden(E_132, A_276) | ~m1_subset_1(E_132, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277), a_2_0_orders_2('#skF_4', A_276)) | ~r1_tarski(A_276, k2_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | r1_tarski(a_2_0_orders_2('#skF_4', A_276), B_277) | ~r1_tarski(A_276, u1_struct_0('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4029, c_845])).
% 15.52/6.79  tff(c_4091, plain, (![E_132, A_276, B_277]: (r2_orders_2('#skF_4', E_132, '#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277)) | ~r2_hidden(E_132, A_276) | ~m1_subset_1(E_132, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_276), B_277), a_2_0_orders_2('#skF_4', A_276)) | v2_struct_0('#skF_4') | r1_tarski(a_2_0_orders_2('#skF_4', A_276), B_277) | ~r1_tarski(A_276, k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_44, c_42, c_4047])).
% 15.52/6.79  tff(c_26343, plain, (![E_640, A_641, B_642]: (r2_orders_2('#skF_4', E_640, '#skF_1'(a_2_0_orders_2('#skF_4', A_641), B_642)) | ~r2_hidden(E_640, A_641) | ~m1_subset_1(E_640, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_641), B_642), a_2_0_orders_2('#skF_4', A_641)) | r1_tarski(a_2_0_orders_2('#skF_4', A_641), B_642) | ~r1_tarski(A_641, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_4091])).
% 15.52/6.79  tff(c_26371, plain, (![E_640, A_641, B_2]: (r2_orders_2('#skF_4', E_640, '#skF_1'(a_2_0_orders_2('#skF_4', A_641), B_2)) | ~r2_hidden(E_640, A_641) | ~m1_subset_1(E_640, k2_struct_0('#skF_4')) | ~r1_tarski(A_641, k2_struct_0('#skF_4')) | ~r1_tarski(a_2_0_orders_2('#skF_4', A_641), a_2_0_orders_2('#skF_4', A_641)) | r1_tarski(a_2_0_orders_2('#skF_4', A_641), B_2))), inference(resolution, [status(thm)], [c_83, c_26343])).
% 15.52/6.79  tff(c_26405, plain, (![E_643, A_644, B_645]: (r2_orders_2('#skF_4', E_643, '#skF_1'(a_2_0_orders_2('#skF_4', A_644), B_645)) | ~r2_hidden(E_643, A_644) | ~m1_subset_1(E_643, k2_struct_0('#skF_4')) | ~r1_tarski(A_644, k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', A_644), B_645))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_26371])).
% 15.52/6.79  tff(c_18, plain, (![A_10, C_16]: (~r2_orders_2(A_10, C_16, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 15.52/6.79  tff(c_26413, plain, (![A_644, B_645]: (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_644), B_645), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_644), B_645), A_644) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_644), B_645), k2_struct_0('#skF_4')) | ~r1_tarski(A_644, k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', A_644), B_645))), inference(resolution, [status(thm)], [c_26405, c_18])).
% 15.52/6.79  tff(c_26431, plain, (![A_646, B_647]: (~r2_hidden('#skF_1'(a_2_0_orders_2('#skF_4', A_646), B_647), A_646) | ~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', A_646), B_647), k2_struct_0('#skF_4')) | ~r1_tarski(A_646, k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', A_646), B_647))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63, c_26413])).
% 15.52/6.79  tff(c_26440, plain, (![B_517]: (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4')), B_517), k2_struct_0('#skF_4')) | ~r1_tarski(u1_struct_0('#skF_4'), k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', u1_struct_0('#skF_4')), B_517) | ~m1_subset_1(u1_struct_0('#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_17210, c_26431])).
% 15.52/6.79  tff(c_26474, plain, (![B_517]: (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), B_517), k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), B_517) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_194, c_63, c_63, c_63, c_79, c_63, c_63, c_26440])).
% 15.52/6.79  tff(c_26499, plain, (![B_648]: (~m1_subset_1('#skF_1'(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), B_648), k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), B_648))), inference(negUnitSimplification, [status(thm)], [c_50, c_26474])).
% 15.52/6.79  tff(c_26503, plain, (![B_2]: (~m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), B_2))), inference(resolution, [status(thm)], [c_4543, c_26499])).
% 15.52/6.79  tff(c_26524, plain, (![B_649]: (r1_tarski(a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4')), B_649))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_194, c_26503])).
% 15.52/6.79  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 15.52/6.79  tff(c_26687, plain, (a_2_0_orders_2('#skF_4', k2_struct_0('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_26524, c_8])).
% 15.52/6.79  tff(c_26793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_26687])).
% 15.52/6.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.52/6.79  
% 15.52/6.79  Inference rules
% 15.52/6.79  ----------------------
% 15.52/6.79  #Ref     : 0
% 15.52/6.79  #Sup     : 5741
% 15.52/6.79  #Fact    : 0
% 15.52/6.79  #Define  : 0
% 15.52/6.79  #Split   : 5
% 15.52/6.79  #Chain   : 0
% 15.52/6.79  #Close   : 0
% 15.52/6.79  
% 15.52/6.79  Ordering : KBO
% 15.52/6.79  
% 15.52/6.79  Simplification rules
% 15.52/6.79  ----------------------
% 15.52/6.79  #Subsume      : 1846
% 15.52/6.79  #Demod        : 20410
% 15.52/6.79  #Tautology    : 572
% 15.52/6.79  #SimpNegUnit  : 1865
% 15.52/6.79  #BackRed      : 9
% 15.52/6.79  
% 15.52/6.79  #Partial instantiations: 0
% 15.52/6.79  #Strategies tried      : 1
% 15.52/6.79  
% 15.52/6.79  Timing (in seconds)
% 15.52/6.79  ----------------------
% 15.52/6.80  Preprocessing        : 0.34
% 15.52/6.80  Parsing              : 0.18
% 15.52/6.80  CNF conversion       : 0.02
% 15.52/6.80  Main loop            : 5.68
% 15.52/6.80  Inferencing          : 1.15
% 15.52/6.80  Reduction            : 1.84
% 15.52/6.80  Demodulation         : 1.42
% 15.52/6.80  BG Simplification    : 0.14
% 15.52/6.80  Subsumption          : 2.28
% 15.52/6.80  Abstraction          : 0.30
% 15.52/6.80  MUC search           : 0.00
% 15.52/6.80  Cooper               : 0.00
% 15.52/6.80  Total                : 6.06
% 15.52/6.80  Index Insertion      : 0.00
% 15.52/6.80  Index Deletion       : 0.00
% 15.52/6.80  Index Matching       : 0.00
% 15.52/6.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
