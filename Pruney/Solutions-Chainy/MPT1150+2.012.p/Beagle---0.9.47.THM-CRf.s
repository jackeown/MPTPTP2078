%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:25 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  107 (1567 expanded)
%              Number of leaves         :   35 ( 597 expanded)
%              Depth                    :   21
%              Number of atoms          :  288 (4792 expanded)
%              Number of equality atoms :   41 ( 795 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(k1_orders_2,type,(
    k1_orders_2: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

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

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_139,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => k1_orders_2(A,k2_struct_0(A)) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
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

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_orders_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

tff(f_125,axiom,(
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

tff(f_63,axiom,(
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

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_1'(A_47,B_48),B_48)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_74])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_48,plain,(
    v3_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_46,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_44,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_26,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_53,plain,(
    ! [A_39] :
      ( u1_struct_0(A_39) = k2_struct_0(A_39)
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    ! [A_42] :
      ( u1_struct_0(A_42) = k2_struct_0(A_42)
      | ~ l1_orders_2(A_42) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_63,plain,(
    u1_struct_0('#skF_5') = k2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_117,plain,(
    ! [A_75,B_76] :
      ( k1_orders_2(A_75,B_76) = a_2_0_orders_2(A_75,B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_orders_2(A_75)
      | ~ v5_orders_2(A_75)
      | ~ v4_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_120,plain,(
    ! [B_76] :
      ( k1_orders_2('#skF_5',B_76) = a_2_0_orders_2('#skF_5',B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_117])).

tff(c_126,plain,(
    ! [B_76] :
      ( k1_orders_2('#skF_5',B_76) = a_2_0_orders_2('#skF_5',B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_120])).

tff(c_129,plain,(
    ! [B_77] :
      ( k1_orders_2('#skF_5',B_77) = a_2_0_orders_2('#skF_5',B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_126])).

tff(c_135,plain,(
    ! [A_78] :
      ( k1_orders_2('#skF_5',A_78) = a_2_0_orders_2('#skF_5',A_78)
      | ~ r1_tarski(A_78,k2_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_129])).

tff(c_140,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) = a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_79,c_135])).

tff(c_40,plain,(
    k1_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_141,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_40])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_6,B_50] :
      ( r2_hidden('#skF_2'(A_6),B_50)
      | ~ r1_tarski(A_6,B_50)
      | k1_xboole_0 = A_6 ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_146,plain,(
    ! [A_79,A_80] :
      ( k1_orders_2(A_79,A_80) = a_2_0_orders_2(A_79,A_80)
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79)
      | ~ r1_tarski(A_80,u1_struct_0(A_79)) ) ),
    inference(resolution,[status(thm)],[c_12,c_117])).

tff(c_154,plain,(
    ! [A_79] :
      ( k1_orders_2(A_79,u1_struct_0(A_79)) = a_2_0_orders_2(A_79,u1_struct_0(A_79))
      | ~ l1_orders_2(A_79)
      | ~ v5_orders_2(A_79)
      | ~ v4_orders_2(A_79)
      | ~ v3_orders_2(A_79)
      | v2_struct_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_79,c_146])).

tff(c_173,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k1_orders_2(A_82,B_83),k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_188,plain,(
    ! [B_83] :
      ( m1_subset_1(k1_orders_2('#skF_5',B_83),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_173])).

tff(c_195,plain,(
    ! [B_83] :
      ( m1_subset_1(k1_orders_2('#skF_5',B_83),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_188])).

tff(c_197,plain,(
    ! [B_84] :
      ( m1_subset_1(k1_orders_2('#skF_5',B_84),k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_195])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_216,plain,(
    ! [B_85] :
      ( r1_tarski(k1_orders_2('#skF_5',B_85),k2_struct_0('#skF_5'))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_197,c_10])).

tff(c_227,plain,
    ( r1_tarski(a_2_0_orders_2('#skF_5',u1_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_216])).

tff(c_235,plain,
    ( r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_63,c_63,c_227])).

tff(c_236,plain,
    ( r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),k2_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_235])).

tff(c_254,plain,(
    ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_257,plain,(
    ~ r1_tarski(k2_struct_0('#skF_5'),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_12,c_254])).

tff(c_261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_257])).

tff(c_263,plain,(
    m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_237,plain,(
    ! [A_86,B_87,C_88] :
      ( '#skF_3'(A_86,B_87,C_88) = A_86
      | ~ r2_hidden(A_86,a_2_0_orders_2(B_87,C_88))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(u1_struct_0(B_87)))
      | ~ l1_orders_2(B_87)
      | ~ v5_orders_2(B_87)
      | ~ v4_orders_2(B_87)
      | ~ v3_orders_2(B_87)
      | v2_struct_0(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1034,plain,(
    ! [B_137,C_138] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2(B_137,C_138)),B_137,C_138) = '#skF_2'(a_2_0_orders_2(B_137,C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(B_137)))
      | ~ l1_orders_2(B_137)
      | ~ v5_orders_2(B_137)
      | ~ v4_orders_2(B_137)
      | ~ v3_orders_2(B_137)
      | v2_struct_0(B_137)
      | a_2_0_orders_2(B_137,C_138) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_237])).

tff(c_1038,plain,(
    ! [C_138] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_138)),'#skF_5',C_138) = '#skF_2'(a_2_0_orders_2('#skF_5',C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_138) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_1034])).

tff(c_1044,plain,(
    ! [C_138] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_138)),'#skF_5',C_138) = '#skF_2'(a_2_0_orders_2('#skF_5',C_138))
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | a_2_0_orders_2('#skF_5',C_138) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_1038])).

tff(c_1082,plain,(
    ! [C_143] :
      ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',C_143)),'#skF_5',C_143) = '#skF_2'(a_2_0_orders_2('#skF_5',C_143))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_struct_0('#skF_5')))
      | a_2_0_orders_2('#skF_5',C_143) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1044])).

tff(c_1088,plain,
    ( '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_263,c_1082])).

tff(c_1100,plain,(
    '#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),'#skF_5',k2_struct_0('#skF_5')) = '#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_1088])).

tff(c_38,plain,(
    ! [A_24,B_25,C_26] :
      ( m1_subset_1('#skF_3'(A_24,B_25,C_26),u1_struct_0(B_25))
      | ~ r2_hidden(A_24,a_2_0_orders_2(B_25,C_26))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(B_25)))
      | ~ l1_orders_2(B_25)
      | ~ v5_orders_2(B_25)
      | ~ v4_orders_2(B_25)
      | ~ v3_orders_2(B_25)
      | v2_struct_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1256,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | ~ m1_subset_1(k2_struct_0('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_38])).

tff(c_1262,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_263,c_63,c_63,c_1256])).

tff(c_1263,plain,
    ( m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1262])).

tff(c_1266,plain,(
    ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1263])).

tff(c_1275,plain,
    ( ~ r1_tarski(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_1266])).

tff(c_1284,plain,(
    a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_1275])).

tff(c_1286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_1284])).

tff(c_1287,plain,(
    m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1263])).

tff(c_88,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53),B_54)
      | ~ r1_tarski(A_53,B_54)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    ! [A_53,B_2,B_54] :
      ( r2_hidden('#skF_2'(A_53),B_2)
      | ~ r1_tarski(B_54,B_2)
      | ~ r1_tarski(A_53,B_54)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_543,plain,(
    ! [A_114,B_115] :
      ( r2_hidden('#skF_2'(A_114),k2_struct_0('#skF_5'))
      | ~ r1_tarski(A_114,k1_orders_2('#skF_5',B_115))
      | k1_xboole_0 = A_114
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_216,c_91])).

tff(c_576,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_2'(k1_orders_2('#skF_5',B_119)),k2_struct_0('#skF_5'))
      | k1_orders_2('#skF_5',B_119) = k1_xboole_0
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k2_struct_0('#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_79,c_543])).

tff(c_588,plain,
    ( r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',u1_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | k1_orders_2('#skF_5',u1_struct_0('#skF_5')) = k1_xboole_0
    | ~ m1_subset_1(u1_struct_0('#skF_5'),k1_zfmisc_1(k2_struct_0('#skF_5')))
    | ~ l1_orders_2('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | ~ v3_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_576])).

tff(c_598,plain,
    ( r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')) = k1_xboole_0
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_263,c_63,c_140,c_63,c_63,c_588])).

tff(c_599,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_141,c_598])).

tff(c_1288,plain,(
    r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1263])).

tff(c_680,plain,(
    ! [B_122,E_123,A_124,C_125] :
      ( r2_orders_2(B_122,E_123,'#skF_3'(A_124,B_122,C_125))
      | ~ r2_hidden(E_123,C_125)
      | ~ m1_subset_1(E_123,u1_struct_0(B_122))
      | ~ r2_hidden(A_124,a_2_0_orders_2(B_122,C_125))
      | ~ m1_subset_1(C_125,k1_zfmisc_1(u1_struct_0(B_122)))
      | ~ l1_orders_2(B_122)
      | ~ v5_orders_2(B_122)
      | ~ v4_orders_2(B_122)
      | ~ v3_orders_2(B_122)
      | v2_struct_0(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1315,plain,(
    ! [B_155,E_156,A_157,A_158] :
      ( r2_orders_2(B_155,E_156,'#skF_3'(A_157,B_155,A_158))
      | ~ r2_hidden(E_156,A_158)
      | ~ m1_subset_1(E_156,u1_struct_0(B_155))
      | ~ r2_hidden(A_157,a_2_0_orders_2(B_155,A_158))
      | ~ l1_orders_2(B_155)
      | ~ v5_orders_2(B_155)
      | ~ v4_orders_2(B_155)
      | ~ v3_orders_2(B_155)
      | v2_struct_0(B_155)
      | ~ r1_tarski(A_158,u1_struct_0(B_155)) ) ),
    inference(resolution,[status(thm)],[c_12,c_680])).

tff(c_1326,plain,(
    ! [E_156] :
      ( r2_orders_2('#skF_5',E_156,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_156,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_156,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5')))
      | ~ l1_orders_2('#skF_5')
      | ~ v5_orders_2('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | ~ v3_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_tarski(k2_struct_0('#skF_5'),u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1100,c_1315])).

tff(c_1340,plain,(
    ! [E_156] :
      ( r2_orders_2('#skF_5',E_156,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_156,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_156,k2_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_63,c_48,c_46,c_44,c_42,c_1288,c_63,c_1326])).

tff(c_1354,plain,(
    ! [E_159] :
      ( r2_orders_2('#skF_5',E_159,'#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))))
      | ~ r2_hidden(E_159,k2_struct_0('#skF_5'))
      | ~ m1_subset_1(E_159,k2_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1340])).

tff(c_18,plain,(
    ! [A_11,C_17] :
      ( ~ r2_orders_2(A_11,C_17,C_17)
      | ~ m1_subset_1(C_17,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1362,plain,
    ( ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5')
    | ~ r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5',k2_struct_0('#skF_5'))),k2_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1354,c_18])).

tff(c_1373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_599,c_42,c_1287,c_63,c_1362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.63  
% 3.69/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.63  %$ r2_orders_2 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_struct_0 > l1_orders_2 > k1_orders_2 > a_2_0_orders_2 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_4 > #skF_3 > #skF_1
% 3.69/1.63  
% 3.69/1.63  %Foreground sorts:
% 3.69/1.63  
% 3.69/1.63  
% 3.69/1.63  %Background operators:
% 3.69/1.63  
% 3.69/1.63  
% 3.69/1.63  %Foreground operators:
% 3.69/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.69/1.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.69/1.63  tff(k1_orders_2, type, k1_orders_2: ($i * $i) > $i).
% 3.69/1.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.63  tff(a_2_0_orders_2, type, a_2_0_orders_2: ($i * $i) > $i).
% 3.69/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.69/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.69/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.69/1.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.69/1.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.69/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.69/1.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.69/1.63  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.69/1.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.69/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.63  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.69/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.69/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.63  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.69/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.69/1.63  
% 3.92/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.92/1.66  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.92/1.66  tff(f_139, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (k1_orders_2(A, k2_struct_0(A)) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_orders_2)).
% 3.92/1.66  tff(f_98, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.92/1.66  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.92/1.66  tff(f_79, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_orders_2(A, B) = a_2_0_orders_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 3.92/1.66  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.92/1.66  tff(f_94, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k1_orders_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_orders_2)).
% 3.92/1.66  tff(f_125, axiom, (![A, B, C]: ((((((~v2_struct_0(B) & v3_orders_2(B)) & v4_orders_2(B)) & v5_orders_2(B)) & l1_orders_2(B)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B)))) => (r2_hidden(A, a_2_0_orders_2(B, C)) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(B)) & (A = D)) & (![E]: (m1_subset_1(E, u1_struct_0(B)) => (r2_hidden(E, C) => r2_orders_2(B, E, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 3.92/1.66  tff(f_63, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.92/1.66  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.66  tff(c_74, plain, (![A_47, B_48]: (~r2_hidden('#skF_1'(A_47, B_48), B_48) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.66  tff(c_79, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_74])).
% 3.92/1.66  tff(c_12, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.92/1.66  tff(c_50, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.92/1.66  tff(c_48, plain, (v3_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.92/1.66  tff(c_46, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.92/1.66  tff(c_44, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.92/1.66  tff(c_42, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.92/1.66  tff(c_26, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.92/1.66  tff(c_53, plain, (![A_39]: (u1_struct_0(A_39)=k2_struct_0(A_39) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.92/1.66  tff(c_59, plain, (![A_42]: (u1_struct_0(A_42)=k2_struct_0(A_42) | ~l1_orders_2(A_42))), inference(resolution, [status(thm)], [c_26, c_53])).
% 3.92/1.66  tff(c_63, plain, (u1_struct_0('#skF_5')=k2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_42, c_59])).
% 3.92/1.66  tff(c_117, plain, (![A_75, B_76]: (k1_orders_2(A_75, B_76)=a_2_0_orders_2(A_75, B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_orders_2(A_75) | ~v5_orders_2(A_75) | ~v4_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.92/1.66  tff(c_120, plain, (![B_76]: (k1_orders_2('#skF_5', B_76)=a_2_0_orders_2('#skF_5', B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_117])).
% 3.92/1.66  tff(c_126, plain, (![B_76]: (k1_orders_2('#skF_5', B_76)=a_2_0_orders_2('#skF_5', B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_120])).
% 3.92/1.66  tff(c_129, plain, (![B_77]: (k1_orders_2('#skF_5', B_77)=a_2_0_orders_2('#skF_5', B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_126])).
% 3.92/1.66  tff(c_135, plain, (![A_78]: (k1_orders_2('#skF_5', A_78)=a_2_0_orders_2('#skF_5', A_78) | ~r1_tarski(A_78, k2_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_12, c_129])).
% 3.92/1.66  tff(c_140, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))=a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_79, c_135])).
% 3.92/1.66  tff(c_40, plain, (k1_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.92/1.66  tff(c_141, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_40])).
% 3.92/1.66  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.92/1.66  tff(c_80, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.66  tff(c_86, plain, (![A_6, B_50]: (r2_hidden('#skF_2'(A_6), B_50) | ~r1_tarski(A_6, B_50) | k1_xboole_0=A_6)), inference(resolution, [status(thm)], [c_8, c_80])).
% 3.92/1.66  tff(c_146, plain, (![A_79, A_80]: (k1_orders_2(A_79, A_80)=a_2_0_orders_2(A_79, A_80) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79) | ~r1_tarski(A_80, u1_struct_0(A_79)))), inference(resolution, [status(thm)], [c_12, c_117])).
% 3.92/1.66  tff(c_154, plain, (![A_79]: (k1_orders_2(A_79, u1_struct_0(A_79))=a_2_0_orders_2(A_79, u1_struct_0(A_79)) | ~l1_orders_2(A_79) | ~v5_orders_2(A_79) | ~v4_orders_2(A_79) | ~v3_orders_2(A_79) | v2_struct_0(A_79))), inference(resolution, [status(thm)], [c_79, c_146])).
% 3.92/1.66  tff(c_173, plain, (![A_82, B_83]: (m1_subset_1(k1_orders_2(A_82, B_83), k1_zfmisc_1(u1_struct_0(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.92/1.66  tff(c_188, plain, (![B_83]: (m1_subset_1(k1_orders_2('#skF_5', B_83), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_63, c_173])).
% 3.92/1.66  tff(c_195, plain, (![B_83]: (m1_subset_1(k1_orders_2('#skF_5', B_83), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_83, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_188])).
% 3.92/1.66  tff(c_197, plain, (![B_84]: (m1_subset_1(k1_orders_2('#skF_5', B_84), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~m1_subset_1(B_84, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_195])).
% 3.92/1.66  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.92/1.66  tff(c_216, plain, (![B_85]: (r1_tarski(k1_orders_2('#skF_5', B_85), k2_struct_0('#skF_5')) | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_197, c_10])).
% 3.92/1.66  tff(c_227, plain, (r1_tarski(a_2_0_orders_2('#skF_5', u1_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_154, c_216])).
% 3.92/1.66  tff(c_235, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_63, c_63, c_227])).
% 3.92/1.66  tff(c_236, plain, (r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), k2_struct_0('#skF_5')) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_50, c_235])).
% 3.92/1.66  tff(c_254, plain, (~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_236])).
% 3.92/1.66  tff(c_257, plain, (~r1_tarski(k2_struct_0('#skF_5'), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_12, c_254])).
% 3.92/1.66  tff(c_261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_257])).
% 3.92/1.66  tff(c_263, plain, (m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_236])).
% 3.92/1.66  tff(c_237, plain, (![A_86, B_87, C_88]: ('#skF_3'(A_86, B_87, C_88)=A_86 | ~r2_hidden(A_86, a_2_0_orders_2(B_87, C_88)) | ~m1_subset_1(C_88, k1_zfmisc_1(u1_struct_0(B_87))) | ~l1_orders_2(B_87) | ~v5_orders_2(B_87) | ~v4_orders_2(B_87) | ~v3_orders_2(B_87) | v2_struct_0(B_87))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.92/1.66  tff(c_1034, plain, (![B_137, C_138]: ('#skF_3'('#skF_2'(a_2_0_orders_2(B_137, C_138)), B_137, C_138)='#skF_2'(a_2_0_orders_2(B_137, C_138)) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(B_137))) | ~l1_orders_2(B_137) | ~v5_orders_2(B_137) | ~v4_orders_2(B_137) | ~v3_orders_2(B_137) | v2_struct_0(B_137) | a_2_0_orders_2(B_137, C_138)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_237])).
% 3.92/1.66  tff(c_1038, plain, (![C_138]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_138)), '#skF_5', C_138)='#skF_2'(a_2_0_orders_2('#skF_5', C_138)) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_138)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63, c_1034])).
% 3.92/1.66  tff(c_1044, plain, (![C_138]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_138)), '#skF_5', C_138)='#skF_2'(a_2_0_orders_2('#skF_5', C_138)) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | a_2_0_orders_2('#skF_5', C_138)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_1038])).
% 3.92/1.66  tff(c_1082, plain, (![C_143]: ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', C_143)), '#skF_5', C_143)='#skF_2'(a_2_0_orders_2('#skF_5', C_143)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', C_143)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_50, c_1044])).
% 3.92/1.66  tff(c_1088, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_263, c_1082])).
% 3.92/1.66  tff(c_1100, plain, ('#skF_3'('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), '#skF_5', k2_struct_0('#skF_5'))='#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_141, c_1088])).
% 3.92/1.66  tff(c_38, plain, (![A_24, B_25, C_26]: (m1_subset_1('#skF_3'(A_24, B_25, C_26), u1_struct_0(B_25)) | ~r2_hidden(A_24, a_2_0_orders_2(B_25, C_26)) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(B_25))) | ~l1_orders_2(B_25) | ~v5_orders_2(B_25) | ~v4_orders_2(B_25) | ~v3_orders_2(B_25) | v2_struct_0(B_25))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.92/1.66  tff(c_1256, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~m1_subset_1(k2_struct_0('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1100, c_38])).
% 3.92/1.66  tff(c_1262, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_263, c_63, c_63, c_1256])).
% 3.92/1.66  tff(c_1263, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1262])).
% 3.92/1.66  tff(c_1266, plain, (~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_1263])).
% 3.92/1.66  tff(c_1275, plain, (~r1_tarski(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_86, c_1266])).
% 3.92/1.66  tff(c_1284, plain, (a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_79, c_1275])).
% 3.92/1.66  tff(c_1286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_1284])).
% 3.92/1.66  tff(c_1287, plain, (m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_1263])).
% 3.92/1.66  tff(c_88, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53), B_54) | ~r1_tarski(A_53, B_54) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_8, c_80])).
% 3.92/1.66  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.92/1.66  tff(c_91, plain, (![A_53, B_2, B_54]: (r2_hidden('#skF_2'(A_53), B_2) | ~r1_tarski(B_54, B_2) | ~r1_tarski(A_53, B_54) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_88, c_2])).
% 3.92/1.66  tff(c_543, plain, (![A_114, B_115]: (r2_hidden('#skF_2'(A_114), k2_struct_0('#skF_5')) | ~r1_tarski(A_114, k1_orders_2('#skF_5', B_115)) | k1_xboole_0=A_114 | ~m1_subset_1(B_115, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_216, c_91])).
% 3.92/1.66  tff(c_576, plain, (![B_119]: (r2_hidden('#skF_2'(k1_orders_2('#skF_5', B_119)), k2_struct_0('#skF_5')) | k1_orders_2('#skF_5', B_119)=k1_xboole_0 | ~m1_subset_1(B_119, k1_zfmisc_1(k2_struct_0('#skF_5'))))), inference(resolution, [status(thm)], [c_79, c_543])).
% 3.92/1.66  tff(c_588, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', u1_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | k1_orders_2('#skF_5', u1_struct_0('#skF_5'))=k1_xboole_0 | ~m1_subset_1(u1_struct_0('#skF_5'), k1_zfmisc_1(k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_154, c_576])).
% 3.92/1.66  tff(c_598, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))=k1_xboole_0 | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_263, c_63, c_140, c_63, c_63, c_588])).
% 3.92/1.66  tff(c_599, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_50, c_141, c_598])).
% 3.92/1.66  tff(c_1288, plain, (r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_1263])).
% 3.92/1.66  tff(c_680, plain, (![B_122, E_123, A_124, C_125]: (r2_orders_2(B_122, E_123, '#skF_3'(A_124, B_122, C_125)) | ~r2_hidden(E_123, C_125) | ~m1_subset_1(E_123, u1_struct_0(B_122)) | ~r2_hidden(A_124, a_2_0_orders_2(B_122, C_125)) | ~m1_subset_1(C_125, k1_zfmisc_1(u1_struct_0(B_122))) | ~l1_orders_2(B_122) | ~v5_orders_2(B_122) | ~v4_orders_2(B_122) | ~v3_orders_2(B_122) | v2_struct_0(B_122))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.92/1.66  tff(c_1315, plain, (![B_155, E_156, A_157, A_158]: (r2_orders_2(B_155, E_156, '#skF_3'(A_157, B_155, A_158)) | ~r2_hidden(E_156, A_158) | ~m1_subset_1(E_156, u1_struct_0(B_155)) | ~r2_hidden(A_157, a_2_0_orders_2(B_155, A_158)) | ~l1_orders_2(B_155) | ~v5_orders_2(B_155) | ~v4_orders_2(B_155) | ~v3_orders_2(B_155) | v2_struct_0(B_155) | ~r1_tarski(A_158, u1_struct_0(B_155)))), inference(resolution, [status(thm)], [c_12, c_680])).
% 3.92/1.66  tff(c_1326, plain, (![E_156]: (r2_orders_2('#skF_5', E_156, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_156, k2_struct_0('#skF_5')) | ~m1_subset_1(E_156, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))) | ~l1_orders_2('#skF_5') | ~v5_orders_2('#skF_5') | ~v4_orders_2('#skF_5') | ~v3_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~r1_tarski(k2_struct_0('#skF_5'), u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1100, c_1315])).
% 3.92/1.66  tff(c_1340, plain, (![E_156]: (r2_orders_2('#skF_5', E_156, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_156, k2_struct_0('#skF_5')) | ~m1_subset_1(E_156, k2_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_63, c_48, c_46, c_44, c_42, c_1288, c_63, c_1326])).
% 3.92/1.66  tff(c_1354, plain, (![E_159]: (r2_orders_2('#skF_5', E_159, '#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5')))) | ~r2_hidden(E_159, k2_struct_0('#skF_5')) | ~m1_subset_1(E_159, k2_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_50, c_1340])).
% 3.92/1.66  tff(c_18, plain, (![A_11, C_17]: (~r2_orders_2(A_11, C_17, C_17) | ~m1_subset_1(C_17, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.66  tff(c_1362, plain, (~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5') | ~r2_hidden('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5')) | ~m1_subset_1('#skF_2'(a_2_0_orders_2('#skF_5', k2_struct_0('#skF_5'))), k2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_1354, c_18])).
% 3.92/1.66  tff(c_1373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1287, c_599, c_42, c_1287, c_63, c_1362])).
% 3.92/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.66  
% 3.92/1.66  Inference rules
% 3.92/1.66  ----------------------
% 3.92/1.66  #Ref     : 0
% 3.92/1.66  #Sup     : 291
% 3.92/1.66  #Fact    : 0
% 3.92/1.66  #Define  : 0
% 3.92/1.66  #Split   : 5
% 3.92/1.66  #Chain   : 0
% 3.92/1.66  #Close   : 0
% 3.92/1.66  
% 3.92/1.66  Ordering : KBO
% 3.92/1.66  
% 3.92/1.66  Simplification rules
% 3.92/1.66  ----------------------
% 3.92/1.66  #Subsume      : 29
% 3.92/1.66  #Demod        : 456
% 3.92/1.66  #Tautology    : 101
% 3.92/1.66  #SimpNegUnit  : 48
% 3.92/1.66  #BackRed      : 14
% 3.92/1.66  
% 3.92/1.66  #Partial instantiations: 0
% 3.92/1.66  #Strategies tried      : 1
% 3.92/1.66  
% 3.92/1.66  Timing (in seconds)
% 3.92/1.66  ----------------------
% 3.92/1.66  Preprocessing        : 0.33
% 3.92/1.66  Parsing              : 0.17
% 3.92/1.66  CNF conversion       : 0.02
% 3.92/1.66  Main loop            : 0.51
% 3.92/1.66  Inferencing          : 0.18
% 3.92/1.66  Reduction            : 0.16
% 3.92/1.66  Demodulation         : 0.11
% 3.92/1.66  BG Simplification    : 0.03
% 3.92/1.66  Subsumption          : 0.10
% 3.92/1.66  Abstraction          : 0.03
% 3.92/1.66  MUC search           : 0.00
% 3.92/1.66  Cooper               : 0.00
% 3.92/1.66  Total                : 0.88
% 3.92/1.66  Index Insertion      : 0.00
% 3.92/1.66  Index Deletion       : 0.00
% 3.92/1.66  Index Matching       : 0.00
% 3.92/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
