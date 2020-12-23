%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:45 EST 2020

% Result     : Theorem 50.49s
% Output     : CNFRefutation 50.75s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 471 expanded)
%              Number of leaves         :   38 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  375 (1340 expanded)
%              Number of equality atoms :   24 (  52 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B,C] :
            ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
           => ( r2_hidden(B,k1_tops_1(A,C))
            <=> ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & v3_pre_topc(D,A)
                  & r1_tarski(D,C)
                  & r2_hidden(B,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k1_tops_1(A,B),k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

tff(c_58,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_56,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_126488,plain,(
    ! [A_1986,B_1987] :
      ( v3_pre_topc(k1_tops_1(A_1986,B_1987),A_1986)
      | ~ m1_subset_1(B_1987,k1_zfmisc_1(u1_struct_0(A_1986)))
      | ~ l1_pre_topc(A_1986)
      | ~ v2_pre_topc(A_1986) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_126505,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_126488])).

tff(c_126520,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_126505])).

tff(c_82,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(A_70,B_71)
      | ~ m1_subset_1(A_70,k1_zfmisc_1(B_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_90,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_82])).

tff(c_125385,plain,(
    ! [A_1892,C_1893,B_1894] :
      ( r1_tarski(A_1892,C_1893)
      | ~ r1_tarski(B_1894,C_1893)
      | ~ r1_tarski(A_1892,B_1894) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_125390,plain,(
    ! [A_1892] :
      ( r1_tarski(A_1892,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1892,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_125385])).

tff(c_123795,plain,(
    ! [A_1771,C_1772,B_1773] :
      ( r1_tarski(A_1771,C_1772)
      | ~ r1_tarski(B_1773,C_1772)
      | ~ r1_tarski(A_1771,B_1773) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_123803,plain,(
    ! [A_1774] :
      ( r1_tarski(A_1774,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1774,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_123795])).

tff(c_123347,plain,(
    ! [A_1752,B_1753] :
      ( r1_tarski(k1_tops_1(A_1752,B_1753),B_1753)
      | ~ m1_subset_1(B_1753,k1_zfmisc_1(u1_struct_0(A_1752)))
      | ~ l1_pre_topc(A_1752) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_123364,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_123347])).

tff(c_123379,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_123364])).

tff(c_70,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_92,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_122363,plain,(
    ! [A_1674,C_1675,B_1676] :
      ( r1_tarski(A_1674,C_1675)
      | ~ r1_tarski(B_1676,C_1675)
      | ~ r1_tarski(A_1674,B_1676) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_122384,plain,(
    ! [A_1679] :
      ( r1_tarski(A_1679,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1679,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_122363])).

tff(c_36,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(A_35,k1_zfmisc_1(B_36))
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_74,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | v3_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_93,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_66,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_91,plain,(
    r2_hidden('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_78,plain,
    ( r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_117,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_161,plain,(
    ! [C_84,B_85,A_86] :
      ( r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,(
    ! [B_85] :
      ( r2_hidden('#skF_3',B_85)
      | ~ r1_tarski('#skF_5',B_85) ) ),
    inference(resolution,[status(thm)],[c_91,c_161])).

tff(c_60,plain,(
    ! [D_66] :
      ( ~ r2_hidden('#skF_3',D_66)
      | ~ r1_tarski(D_66,'#skF_4')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_694,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_702,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_167,c_694])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_203,plain,(
    ! [A_90,B_91] :
      ( k3_subset_1(A_90,k3_subset_1(A_90,B_91)) = B_91
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_210,plain,(
    k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_117,c_203])).

tff(c_339,plain,(
    ! [A_101,B_102] :
      ( k4_xboole_0(A_101,B_102) = k3_subset_1(A_101,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_349,plain,(
    k4_xboole_0(u1_struct_0('#skF_2'),'#skF_5') = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_117,c_339])).

tff(c_756,plain,(
    ! [A_133,B_134,C_135] :
      ( k7_subset_1(A_133,B_134,C_135) = k4_xboole_0(B_134,C_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_133)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2391,plain,(
    ! [B_183,A_184,C_185] :
      ( k7_subset_1(B_183,A_184,C_185) = k4_xboole_0(A_184,C_185)
      | ~ r1_tarski(A_184,B_183) ) ),
    inference(resolution,[status(thm)],[c_36,c_756])).

tff(c_2496,plain,(
    ! [B_186,C_187] : k7_subset_1(B_186,B_186,C_187) = k4_xboole_0(B_186,C_187) ),
    inference(resolution,[status(thm)],[c_12,c_2391])).

tff(c_622,plain,(
    ! [A_122,B_123,C_124] :
      ( m1_subset_1(k7_subset_1(A_122,B_123,C_124),k1_zfmisc_1(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_637,plain,(
    ! [A_122,B_123,C_124] :
      ( r1_tarski(k7_subset_1(A_122,B_123,C_124),A_122)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_622,c_34])).

tff(c_2530,plain,(
    ! [B_189,C_190] :
      ( r1_tarski(k4_xboole_0(B_189,C_190),B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(B_189)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2496,c_637])).

tff(c_2612,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_2530])).

tff(c_4670,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2612])).

tff(c_4673,plain,(
    ~ r1_tarski(u1_struct_0('#skF_2'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_4670])).

tff(c_4677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4673])).

tff(c_4679,plain,(
    m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2612])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] :
      ( m1_subset_1(k7_subset_1(A_15,B_16,C_17),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4253,plain,(
    ! [B_222,C_223] :
      ( m1_subset_1(k4_xboole_0(B_222,C_223),k1_zfmisc_1(B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1(B_222)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2496,c_20])).

tff(c_4307,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1(u1_struct_0('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_4253])).

tff(c_5075,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4679,c_4307])).

tff(c_1906,plain,(
    ! [B_166,A_167] :
      ( v4_pre_topc(B_166,A_167)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_167),B_166),A_167)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1916,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ v3_pre_topc('#skF_5','#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_1906])).

tff(c_1922,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_93,c_1916])).

tff(c_25838,plain,(
    v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'),'#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5075,c_1922])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k3_subset_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1337,plain,(
    ! [A_148,B_149] :
      ( k2_pre_topc(A_148,B_149) = B_149
      | ~ v4_pre_topc(B_149,A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1387,plain,(
    ! [A_148,B_14] :
      ( k2_pre_topc(A_148,k3_subset_1(u1_struct_0(A_148),B_14)) = k3_subset_1(u1_struct_0(A_148),B_14)
      | ~ v4_pre_topc(k3_subset_1(u1_struct_0(A_148),B_14),A_148)
      | ~ l1_pre_topc(A_148)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_148))) ) ),
    inference(resolution,[status(thm)],[c_18,c_1337])).

tff(c_25841,plain,
    ( k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_25838,c_1387])).

tff(c_25850,plain,(
    k2_pre_topc('#skF_2',k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k3_subset_1(u1_struct_0('#skF_2'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_56,c_25841])).

tff(c_42,plain,(
    ! [A_40,B_42] :
      ( k3_subset_1(u1_struct_0(A_40),k2_pre_topc(A_40,k3_subset_1(u1_struct_0(A_40),B_42))) = k1_tops_1(A_40,B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_25875,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k3_subset_1(u1_struct_0('#skF_2'),'#skF_5')) = k1_tops_1('#skF_2','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25850,c_42])).

tff(c_25893,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_210,c_25875])).

tff(c_1014,plain,(
    ! [A_142,B_143] :
      ( r1_tarski(k1_tops_1(A_142,B_143),B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1026,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_1014])).

tff(c_1042,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1026])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1104,plain,
    ( k1_tops_1('#skF_2','#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1042,c_8])).

tff(c_1509,plain,(
    ~ r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_25944,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25893,c_1509])).

tff(c_25992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_25944])).

tff(c_25993,plain,(
    k1_tops_1('#skF_2','#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_52,plain,(
    ! [A_51,B_55,C_57] :
      ( r1_tarski(k1_tops_1(A_51,B_55),k1_tops_1(A_51,C_57))
      | ~ r1_tarski(B_55,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_27487,plain,(
    ! [A_599,B_600,C_601] :
      ( r1_tarski(k1_tops_1(A_599,B_600),k1_tops_1(A_599,C_601))
      | ~ r1_tarski(B_600,C_601)
      | ~ m1_subset_1(C_601,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ m1_subset_1(B_600,k1_zfmisc_1(u1_struct_0(A_599)))
      | ~ l1_pre_topc(A_599) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(A_8,C_10)
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36045,plain,(
    ! [A_754,A_755,C_756,B_757] :
      ( r1_tarski(A_754,k1_tops_1(A_755,C_756))
      | ~ r1_tarski(A_754,k1_tops_1(A_755,B_757))
      | ~ r1_tarski(B_757,C_756)
      | ~ m1_subset_1(C_756,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ m1_subset_1(B_757,k1_zfmisc_1(u1_struct_0(A_755)))
      | ~ l1_pre_topc(A_755) ) ),
    inference(resolution,[status(thm)],[c_27487,c_14])).

tff(c_120909,plain,(
    ! [A_1652,B_1653,C_1654,C_1655] :
      ( r1_tarski(k1_tops_1(A_1652,B_1653),k1_tops_1(A_1652,C_1654))
      | ~ r1_tarski(C_1655,C_1654)
      | ~ m1_subset_1(C_1654,k1_zfmisc_1(u1_struct_0(A_1652)))
      | ~ r1_tarski(B_1653,C_1655)
      | ~ m1_subset_1(C_1655,k1_zfmisc_1(u1_struct_0(A_1652)))
      | ~ m1_subset_1(B_1653,k1_zfmisc_1(u1_struct_0(A_1652)))
      | ~ l1_pre_topc(A_1652) ) ),
    inference(resolution,[status(thm)],[c_52,c_36045])).

tff(c_122034,plain,(
    ! [A_1658,B_1659] :
      ( r1_tarski(k1_tops_1(A_1658,B_1659),k1_tops_1(A_1658,'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_1658)))
      | ~ r1_tarski(B_1659,'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_1658)))
      | ~ m1_subset_1(B_1659,k1_zfmisc_1(u1_struct_0(A_1658)))
      | ~ l1_pre_topc(A_1658) ) ),
    inference(resolution,[status(thm)],[c_92,c_120909])).

tff(c_122101,plain,
    ( r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r1_tarski('#skF_5','#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_25993,c_122034])).

tff(c_122139,plain,(
    r1_tarski('#skF_5',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_117,c_12,c_54,c_122101])).

tff(c_122141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_702,c_122139])).

tff(c_122322,plain,(
    ! [D_1670] :
      ( ~ r2_hidden('#skF_3',D_1670)
      | ~ r1_tarski(D_1670,'#skF_4')
      | ~ v3_pre_topc(D_1670,'#skF_2')
      | ~ m1_subset_1(D_1670,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_122333,plain,
    ( ~ r2_hidden('#skF_3','#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_122322])).

tff(c_122346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_92,c_91,c_122333])).

tff(c_122348,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_122352,plain,(
    ~ r1_tarski('#skF_5',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_122348])).

tff(c_122389,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_122384,c_122352])).

tff(c_122396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_122389])).

tff(c_122397,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_123697,plain,(
    ! [A_1758,B_1759] :
      ( v3_pre_topc(k1_tops_1(A_1758,B_1759),A_1758)
      | ~ m1_subset_1(B_1759,k1_zfmisc_1(u1_struct_0(A_1758)))
      | ~ l1_pre_topc(A_1758)
      | ~ v2_pre_topc(A_1758) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_123720,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_123697])).

tff(c_123744,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_123720])).

tff(c_122473,plain,(
    ! [A_1692,C_1693,B_1694] :
      ( r1_tarski(A_1692,C_1693)
      | ~ r1_tarski(B_1694,C_1693)
      | ~ r1_tarski(A_1692,B_1694) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_122484,plain,(
    ! [A_1692] :
      ( r1_tarski(A_1692,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1692,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_122473])).

tff(c_122398,plain,(
    ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [D_66] :
      ( ~ r2_hidden('#skF_3',D_66)
      | ~ r1_tarski(D_66,'#skF_4')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v3_pre_topc('#skF_5','#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_122430,plain,(
    ! [D_1686] :
      ( ~ r2_hidden('#skF_3',D_1686)
      | ~ r1_tarski(D_1686,'#skF_4')
      | ~ v3_pre_topc(D_1686,'#skF_2')
      | ~ m1_subset_1(D_1686,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122398,c_72])).

tff(c_122993,plain,(
    ! [A_1737] :
      ( ~ r2_hidden('#skF_3',A_1737)
      | ~ r1_tarski(A_1737,'#skF_4')
      | ~ v3_pre_topc(A_1737,'#skF_2')
      | ~ r1_tarski(A_1737,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_122430])).

tff(c_123021,plain,(
    ! [A_1692] :
      ( ~ r2_hidden('#skF_3',A_1692)
      | ~ v3_pre_topc(A_1692,'#skF_2')
      | ~ r1_tarski(A_1692,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_122484,c_122993])).

tff(c_123747,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_123744,c_123021])).

tff(c_123751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123379,c_122397,c_123747])).

tff(c_123752,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_123774,plain,(
    ! [C_1766,B_1767,A_1768] :
      ( r2_hidden(C_1766,B_1767)
      | ~ r2_hidden(C_1766,A_1768)
      | ~ r1_tarski(A_1768,B_1767) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_123782,plain,(
    ! [B_1767] :
      ( r2_hidden('#skF_3',B_1767)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_1767) ) ),
    inference(resolution,[status(thm)],[c_123752,c_123774])).

tff(c_123813,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_123803,c_123782])).

tff(c_123825,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_123813])).

tff(c_124221,plain,(
    ! [A_1816,B_1817] :
      ( r1_tarski(k1_tops_1(A_1816,B_1817),B_1817)
      | ~ m1_subset_1(B_1817,k1_zfmisc_1(u1_struct_0(A_1816)))
      | ~ l1_pre_topc(A_1816) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_124236,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_124221])).

tff(c_124248,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_124236])).

tff(c_124250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123825,c_124248])).

tff(c_124252,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_123813])).

tff(c_124586,plain,(
    ! [A_1853,A_1854] :
      ( r1_tarski(A_1853,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1853,A_1854)
      | ~ r1_tarski(A_1854,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_123803,c_14])).

tff(c_124592,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_124252,c_124586])).

tff(c_124603,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_124592])).

tff(c_123753,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_68,plain,(
    ! [D_66] :
      ( ~ r2_hidden('#skF_3',D_66)
      | ~ r1_tarski(D_66,'#skF_4')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r1_tarski('#skF_5','#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124447,plain,(
    ! [D_1838] :
      ( ~ r2_hidden('#skF_3',D_1838)
      | ~ r1_tarski(D_1838,'#skF_4')
      | ~ v3_pre_topc(D_1838,'#skF_2')
      | ~ m1_subset_1(D_1838,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123753,c_68])).

tff(c_125155,plain,(
    ! [A_1876] :
      ( ~ r2_hidden('#skF_3',A_1876)
      | ~ r1_tarski(A_1876,'#skF_4')
      | ~ v3_pre_topc(A_1876,'#skF_2')
      | ~ r1_tarski(A_1876,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_124447])).

tff(c_125173,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_124603,c_125155])).

tff(c_125199,plain,(
    ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124252,c_123752,c_125173])).

tff(c_125323,plain,(
    ! [A_1884,B_1885] :
      ( v3_pre_topc(k1_tops_1(A_1884,B_1885),A_1884)
      | ~ m1_subset_1(B_1885,k1_zfmisc_1(u1_struct_0(A_1884)))
      | ~ l1_pre_topc(A_1884)
      | ~ v2_pre_topc(A_1884) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_125343,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_125323])).

tff(c_125359,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_125343])).

tff(c_125361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125199,c_125359])).

tff(c_125362,plain,(
    r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_125399,plain,(
    ! [C_1896,B_1897,A_1898] :
      ( r2_hidden(C_1896,B_1897)
      | ~ r2_hidden(C_1896,A_1898)
      | ~ r1_tarski(A_1898,B_1897) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125406,plain,(
    ! [B_1899] :
      ( r2_hidden('#skF_3',B_1899)
      | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),B_1899) ) ),
    inference(resolution,[status(thm)],[c_125362,c_125399])).

tff(c_125415,plain,
    ( r2_hidden('#skF_3',u1_struct_0('#skF_2'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_125390,c_125406])).

tff(c_125419,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_125415])).

tff(c_125690,plain,(
    ! [A_1932,B_1933] :
      ( r1_tarski(k1_tops_1(A_1932,B_1933),B_1933)
      | ~ m1_subset_1(B_1933,k1_zfmisc_1(u1_struct_0(A_1932)))
      | ~ l1_pre_topc(A_1932) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_125701,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_125690])).

tff(c_125707,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_125701])).

tff(c_125709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125419,c_125707])).

tff(c_125711,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_125415])).

tff(c_125392,plain,(
    ! [A_1895] :
      ( r1_tarski(A_1895,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1895,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_125385])).

tff(c_125973,plain,(
    ! [A_1960,A_1961] :
      ( r1_tarski(A_1960,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_1960,A_1961)
      | ~ r1_tarski(A_1961,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_125392,c_14])).

tff(c_125977,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_125711,c_125973])).

tff(c_125987,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_125977])).

tff(c_125363,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_64,plain,(
    ! [D_66] :
      ( ~ r2_hidden('#skF_3',D_66)
      | ~ r1_tarski(D_66,'#skF_4')
      | ~ v3_pre_topc(D_66,'#skF_2')
      | ~ m1_subset_1(D_66,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden('#skF_3','#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_125900,plain,(
    ! [D_1955] :
      ( ~ r2_hidden('#skF_3',D_1955)
      | ~ r1_tarski(D_1955,'#skF_4')
      | ~ v3_pre_topc(D_1955,'#skF_2')
      | ~ m1_subset_1(D_1955,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_125363,c_64])).

tff(c_126730,plain,(
    ! [A_2000] :
      ( ~ r2_hidden('#skF_3',A_2000)
      | ~ r1_tarski(A_2000,'#skF_4')
      | ~ v3_pre_topc(A_2000,'#skF_2')
      | ~ r1_tarski(A_2000,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_125900])).

tff(c_126756,plain,
    ( ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_125987,c_126730])).

tff(c_126785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126520,c_125711,c_125362,c_126756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 50.49/39.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.49/39.58  
% 50.49/39.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.49/39.59  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 50.49/39.59  
% 50.49/39.59  %Foreground sorts:
% 50.49/39.59  
% 50.49/39.59  
% 50.49/39.59  %Background operators:
% 50.49/39.59  
% 50.49/39.59  
% 50.49/39.59  %Foreground operators:
% 50.49/39.59  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 50.49/39.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 50.49/39.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 50.49/39.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 50.49/39.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 50.49/39.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 50.49/39.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 50.49/39.59  tff('#skF_5', type, '#skF_5': $i).
% 50.49/39.59  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 50.49/39.59  tff('#skF_2', type, '#skF_2': $i).
% 50.49/39.59  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 50.49/39.59  tff('#skF_3', type, '#skF_3': $i).
% 50.49/39.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 50.49/39.59  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 50.49/39.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 50.49/39.59  tff('#skF_4', type, '#skF_4': $i).
% 50.49/39.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 50.49/39.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 50.49/39.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 50.49/39.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 50.49/39.59  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 50.49/39.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 50.49/39.59  
% 50.75/39.61  tff(f_170, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B, C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k1_tops_1(A, C)) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_tops_1)).
% 50.75/39.61  tff(f_123, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_tops_1)).
% 50.75/39.61  tff(f_93, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 50.75/39.61  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 50.75/39.61  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 50.75/39.61  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 50.75/39.61  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 50.75/39.61  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 50.75/39.61  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 50.75/39.61  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 50.75/39.61  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 50.75/39.61  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 50.75/39.61  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 50.75/39.61  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 50.75/39.61  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tops_1)).
% 50.75/39.61  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k1_tops_1(A, B), k1_tops_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_tops_1)).
% 50.75/39.61  tff(c_58, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_56, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_126488, plain, (![A_1986, B_1987]: (v3_pre_topc(k1_tops_1(A_1986, B_1987), A_1986) | ~m1_subset_1(B_1987, k1_zfmisc_1(u1_struct_0(A_1986))) | ~l1_pre_topc(A_1986) | ~v2_pre_topc(A_1986))), inference(cnfTransformation, [status(thm)], [f_123])).
% 50.75/39.61  tff(c_126505, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_126488])).
% 50.75/39.61  tff(c_126520, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_126505])).
% 50.75/39.61  tff(c_82, plain, (![A_70, B_71]: (r1_tarski(A_70, B_71) | ~m1_subset_1(A_70, k1_zfmisc_1(B_71)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 50.75/39.61  tff(c_90, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_82])).
% 50.75/39.61  tff(c_125385, plain, (![A_1892, C_1893, B_1894]: (r1_tarski(A_1892, C_1893) | ~r1_tarski(B_1894, C_1893) | ~r1_tarski(A_1892, B_1894))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.75/39.61  tff(c_125390, plain, (![A_1892]: (r1_tarski(A_1892, u1_struct_0('#skF_2')) | ~r1_tarski(A_1892, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_125385])).
% 50.75/39.61  tff(c_123795, plain, (![A_1771, C_1772, B_1773]: (r1_tarski(A_1771, C_1772) | ~r1_tarski(B_1773, C_1772) | ~r1_tarski(A_1771, B_1773))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.75/39.61  tff(c_123803, plain, (![A_1774]: (r1_tarski(A_1774, u1_struct_0('#skF_2')) | ~r1_tarski(A_1774, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_123795])).
% 50.75/39.61  tff(c_123347, plain, (![A_1752, B_1753]: (r1_tarski(k1_tops_1(A_1752, B_1753), B_1753) | ~m1_subset_1(B_1753, k1_zfmisc_1(u1_struct_0(A_1752))) | ~l1_pre_topc(A_1752))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.75/39.61  tff(c_123364, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_123347])).
% 50.75/39.61  tff(c_123379, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_123364])).
% 50.75/39.61  tff(c_70, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_92, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_70])).
% 50.75/39.61  tff(c_122363, plain, (![A_1674, C_1675, B_1676]: (r1_tarski(A_1674, C_1675) | ~r1_tarski(B_1676, C_1675) | ~r1_tarski(A_1674, B_1676))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.75/39.61  tff(c_122384, plain, (![A_1679]: (r1_tarski(A_1679, u1_struct_0('#skF_2')) | ~r1_tarski(A_1679, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_122363])).
% 50.75/39.61  tff(c_36, plain, (![A_35, B_36]: (m1_subset_1(A_35, k1_zfmisc_1(B_36)) | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 50.75/39.61  tff(c_74, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | v3_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_93, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitLeft, [status(thm)], [c_74])).
% 50.75/39.61  tff(c_66, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_91, plain, (r2_hidden('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_66])).
% 50.75/39.61  tff(c_78, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_117, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_78])).
% 50.75/39.61  tff(c_161, plain, (![C_84, B_85, A_86]: (r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | ~r1_tarski(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.75/39.61  tff(c_167, plain, (![B_85]: (r2_hidden('#skF_3', B_85) | ~r1_tarski('#skF_5', B_85))), inference(resolution, [status(thm)], [c_91, c_161])).
% 50.75/39.61  tff(c_60, plain, (![D_66]: (~r2_hidden('#skF_3', D_66) | ~r1_tarski(D_66, '#skF_4') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_694, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_60])).
% 50.75/39.61  tff(c_702, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_167, c_694])).
% 50.75/39.61  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 50.75/39.61  tff(c_203, plain, (![A_90, B_91]: (k3_subset_1(A_90, k3_subset_1(A_90, B_91))=B_91 | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 50.75/39.61  tff(c_210, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_117, c_203])).
% 50.75/39.61  tff(c_339, plain, (![A_101, B_102]: (k4_xboole_0(A_101, B_102)=k3_subset_1(A_101, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 50.75/39.61  tff(c_349, plain, (k4_xboole_0(u1_struct_0('#skF_2'), '#skF_5')=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(resolution, [status(thm)], [c_117, c_339])).
% 50.75/39.61  tff(c_756, plain, (![A_133, B_134, C_135]: (k7_subset_1(A_133, B_134, C_135)=k4_xboole_0(B_134, C_135) | ~m1_subset_1(B_134, k1_zfmisc_1(A_133)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 50.75/39.61  tff(c_2391, plain, (![B_183, A_184, C_185]: (k7_subset_1(B_183, A_184, C_185)=k4_xboole_0(A_184, C_185) | ~r1_tarski(A_184, B_183))), inference(resolution, [status(thm)], [c_36, c_756])).
% 50.75/39.61  tff(c_2496, plain, (![B_186, C_187]: (k7_subset_1(B_186, B_186, C_187)=k4_xboole_0(B_186, C_187))), inference(resolution, [status(thm)], [c_12, c_2391])).
% 50.75/39.61  tff(c_622, plain, (![A_122, B_123, C_124]: (m1_subset_1(k7_subset_1(A_122, B_123, C_124), k1_zfmisc_1(A_122)) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 50.75/39.61  tff(c_34, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 50.75/39.61  tff(c_637, plain, (![A_122, B_123, C_124]: (r1_tarski(k7_subset_1(A_122, B_123, C_124), A_122) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(resolution, [status(thm)], [c_622, c_34])).
% 50.75/39.61  tff(c_2530, plain, (![B_189, C_190]: (r1_tarski(k4_xboole_0(B_189, C_190), B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(B_189)))), inference(superposition, [status(thm), theory('equality')], [c_2496, c_637])).
% 50.75/39.61  tff(c_2612, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), u1_struct_0('#skF_2')) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_349, c_2530])).
% 50.75/39.61  tff(c_4670, plain, (~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_2612])).
% 50.75/39.61  tff(c_4673, plain, (~r1_tarski(u1_struct_0('#skF_2'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_4670])).
% 50.75/39.61  tff(c_4677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4673])).
% 50.75/39.61  tff(c_4679, plain, (m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_2612])).
% 50.75/39.61  tff(c_20, plain, (![A_15, B_16, C_17]: (m1_subset_1(k7_subset_1(A_15, B_16, C_17), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 50.75/39.61  tff(c_4253, plain, (![B_222, C_223]: (m1_subset_1(k4_xboole_0(B_222, C_223), k1_zfmisc_1(B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1(B_222)))), inference(superposition, [status(thm), theory('equality')], [c_2496, c_20])).
% 50.75/39.61  tff(c_4307, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(u1_struct_0('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_349, c_4253])).
% 50.75/39.61  tff(c_5075, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4679, c_4307])).
% 50.75/39.61  tff(c_1906, plain, (![B_166, A_167]: (v4_pre_topc(B_166, A_167) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_167), B_166), A_167) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(cnfTransformation, [status(thm)], [f_132])).
% 50.75/39.61  tff(c_1916, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~v3_pre_topc('#skF_5', '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_210, c_1906])).
% 50.75/39.61  tff(c_1922, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2') | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_93, c_1916])).
% 50.75/39.61  tff(c_25838, plain, (v4_pre_topc(k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5075, c_1922])).
% 50.75/39.61  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k3_subset_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 50.75/39.61  tff(c_1337, plain, (![A_148, B_149]: (k2_pre_topc(A_148, B_149)=B_149 | ~v4_pre_topc(B_149, A_148) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_108])).
% 50.75/39.61  tff(c_1387, plain, (![A_148, B_14]: (k2_pre_topc(A_148, k3_subset_1(u1_struct_0(A_148), B_14))=k3_subset_1(u1_struct_0(A_148), B_14) | ~v4_pre_topc(k3_subset_1(u1_struct_0(A_148), B_14), A_148) | ~l1_pre_topc(A_148) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_148))))), inference(resolution, [status(thm)], [c_18, c_1337])).
% 50.75/39.61  tff(c_25841, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5') | ~l1_pre_topc('#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_25838, c_1387])).
% 50.75/39.61  tff(c_25850, plain, (k2_pre_topc('#skF_2', k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k3_subset_1(u1_struct_0('#skF_2'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_56, c_25841])).
% 50.75/39.61  tff(c_42, plain, (![A_40, B_42]: (k3_subset_1(u1_struct_0(A_40), k2_pre_topc(A_40, k3_subset_1(u1_struct_0(A_40), B_42)))=k1_tops_1(A_40, B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_40))) | ~l1_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_115])).
% 50.75/39.61  tff(c_25875, plain, (k3_subset_1(u1_struct_0('#skF_2'), k3_subset_1(u1_struct_0('#skF_2'), '#skF_5'))=k1_tops_1('#skF_2', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25850, c_42])).
% 50.75/39.61  tff(c_25893, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_210, c_25875])).
% 50.75/39.61  tff(c_1014, plain, (![A_142, B_143]: (r1_tarski(k1_tops_1(A_142, B_143), B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.75/39.61  tff(c_1026, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_117, c_1014])).
% 50.75/39.61  tff(c_1042, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1026])).
% 50.75/39.61  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 50.75/39.61  tff(c_1104, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(resolution, [status(thm)], [c_1042, c_8])).
% 50.75/39.61  tff(c_1509, plain, (~r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1104])).
% 50.75/39.61  tff(c_25944, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_25893, c_1509])).
% 50.75/39.61  tff(c_25992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_25944])).
% 50.75/39.61  tff(c_25993, plain, (k1_tops_1('#skF_2', '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_1104])).
% 50.75/39.61  tff(c_52, plain, (![A_51, B_55, C_57]: (r1_tarski(k1_tops_1(A_51, B_55), k1_tops_1(A_51, C_57)) | ~r1_tarski(B_55, C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_51))) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_151])).
% 50.75/39.61  tff(c_27487, plain, (![A_599, B_600, C_601]: (r1_tarski(k1_tops_1(A_599, B_600), k1_tops_1(A_599, C_601)) | ~r1_tarski(B_600, C_601) | ~m1_subset_1(C_601, k1_zfmisc_1(u1_struct_0(A_599))) | ~m1_subset_1(B_600, k1_zfmisc_1(u1_struct_0(A_599))) | ~l1_pre_topc(A_599))), inference(cnfTransformation, [status(thm)], [f_151])).
% 50.75/39.61  tff(c_14, plain, (![A_8, C_10, B_9]: (r1_tarski(A_8, C_10) | ~r1_tarski(B_9, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.75/39.61  tff(c_36045, plain, (![A_754, A_755, C_756, B_757]: (r1_tarski(A_754, k1_tops_1(A_755, C_756)) | ~r1_tarski(A_754, k1_tops_1(A_755, B_757)) | ~r1_tarski(B_757, C_756) | ~m1_subset_1(C_756, k1_zfmisc_1(u1_struct_0(A_755))) | ~m1_subset_1(B_757, k1_zfmisc_1(u1_struct_0(A_755))) | ~l1_pre_topc(A_755))), inference(resolution, [status(thm)], [c_27487, c_14])).
% 50.75/39.61  tff(c_120909, plain, (![A_1652, B_1653, C_1654, C_1655]: (r1_tarski(k1_tops_1(A_1652, B_1653), k1_tops_1(A_1652, C_1654)) | ~r1_tarski(C_1655, C_1654) | ~m1_subset_1(C_1654, k1_zfmisc_1(u1_struct_0(A_1652))) | ~r1_tarski(B_1653, C_1655) | ~m1_subset_1(C_1655, k1_zfmisc_1(u1_struct_0(A_1652))) | ~m1_subset_1(B_1653, k1_zfmisc_1(u1_struct_0(A_1652))) | ~l1_pre_topc(A_1652))), inference(resolution, [status(thm)], [c_52, c_36045])).
% 50.75/39.61  tff(c_122034, plain, (![A_1658, B_1659]: (r1_tarski(k1_tops_1(A_1658, B_1659), k1_tops_1(A_1658, '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_1658))) | ~r1_tarski(B_1659, '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_1658))) | ~m1_subset_1(B_1659, k1_zfmisc_1(u1_struct_0(A_1658))) | ~l1_pre_topc(A_1658))), inference(resolution, [status(thm)], [c_92, c_120909])).
% 50.75/39.61  tff(c_122101, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_tarski('#skF_5', '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_25993, c_122034])).
% 50.75/39.61  tff(c_122139, plain, (r1_tarski('#skF_5', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_117, c_12, c_54, c_122101])).
% 50.75/39.61  tff(c_122141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_702, c_122139])).
% 50.75/39.61  tff(c_122322, plain, (![D_1670]: (~r2_hidden('#skF_3', D_1670) | ~r1_tarski(D_1670, '#skF_4') | ~v3_pre_topc(D_1670, '#skF_2') | ~m1_subset_1(D_1670, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_60])).
% 50.75/39.61  tff(c_122333, plain, (~r2_hidden('#skF_3', '#skF_5') | ~r1_tarski('#skF_5', '#skF_4') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_117, c_122322])).
% 50.75/39.61  tff(c_122346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_92, c_91, c_122333])).
% 50.75/39.61  tff(c_122348, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_78])).
% 50.75/39.61  tff(c_122352, plain, (~r1_tarski('#skF_5', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_36, c_122348])).
% 50.75/39.61  tff(c_122389, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_122384, c_122352])).
% 50.75/39.61  tff(c_122396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_122389])).
% 50.75/39.61  tff(c_122397, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_74])).
% 50.75/39.61  tff(c_123697, plain, (![A_1758, B_1759]: (v3_pre_topc(k1_tops_1(A_1758, B_1759), A_1758) | ~m1_subset_1(B_1759, k1_zfmisc_1(u1_struct_0(A_1758))) | ~l1_pre_topc(A_1758) | ~v2_pre_topc(A_1758))), inference(cnfTransformation, [status(thm)], [f_123])).
% 50.75/39.61  tff(c_123720, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_123697])).
% 50.75/39.61  tff(c_123744, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_123720])).
% 50.75/39.61  tff(c_122473, plain, (![A_1692, C_1693, B_1694]: (r1_tarski(A_1692, C_1693) | ~r1_tarski(B_1694, C_1693) | ~r1_tarski(A_1692, B_1694))), inference(cnfTransformation, [status(thm)], [f_44])).
% 50.75/39.61  tff(c_122484, plain, (![A_1692]: (r1_tarski(A_1692, u1_struct_0('#skF_2')) | ~r1_tarski(A_1692, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_122473])).
% 50.75/39.61  tff(c_122398, plain, (~v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_74])).
% 50.75/39.61  tff(c_72, plain, (![D_66]: (~r2_hidden('#skF_3', D_66) | ~r1_tarski(D_66, '#skF_4') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v3_pre_topc('#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_122430, plain, (![D_1686]: (~r2_hidden('#skF_3', D_1686) | ~r1_tarski(D_1686, '#skF_4') | ~v3_pre_topc(D_1686, '#skF_2') | ~m1_subset_1(D_1686, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_122398, c_72])).
% 50.75/39.61  tff(c_122993, plain, (![A_1737]: (~r2_hidden('#skF_3', A_1737) | ~r1_tarski(A_1737, '#skF_4') | ~v3_pre_topc(A_1737, '#skF_2') | ~r1_tarski(A_1737, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_122430])).
% 50.75/39.61  tff(c_123021, plain, (![A_1692]: (~r2_hidden('#skF_3', A_1692) | ~v3_pre_topc(A_1692, '#skF_2') | ~r1_tarski(A_1692, '#skF_4'))), inference(resolution, [status(thm)], [c_122484, c_122993])).
% 50.75/39.61  tff(c_123747, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_123744, c_123021])).
% 50.75/39.61  tff(c_123751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123379, c_122397, c_123747])).
% 50.75/39.61  tff(c_123752, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_70])).
% 50.75/39.61  tff(c_123774, plain, (![C_1766, B_1767, A_1768]: (r2_hidden(C_1766, B_1767) | ~r2_hidden(C_1766, A_1768) | ~r1_tarski(A_1768, B_1767))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.75/39.61  tff(c_123782, plain, (![B_1767]: (r2_hidden('#skF_3', B_1767) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_1767))), inference(resolution, [status(thm)], [c_123752, c_123774])).
% 50.75/39.61  tff(c_123813, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_123803, c_123782])).
% 50.75/39.61  tff(c_123825, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_123813])).
% 50.75/39.61  tff(c_124221, plain, (![A_1816, B_1817]: (r1_tarski(k1_tops_1(A_1816, B_1817), B_1817) | ~m1_subset_1(B_1817, k1_zfmisc_1(u1_struct_0(A_1816))) | ~l1_pre_topc(A_1816))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.75/39.61  tff(c_124236, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_124221])).
% 50.75/39.61  tff(c_124248, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_124236])).
% 50.75/39.61  tff(c_124250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123825, c_124248])).
% 50.75/39.61  tff(c_124252, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_123813])).
% 50.75/39.61  tff(c_124586, plain, (![A_1853, A_1854]: (r1_tarski(A_1853, u1_struct_0('#skF_2')) | ~r1_tarski(A_1853, A_1854) | ~r1_tarski(A_1854, '#skF_4'))), inference(resolution, [status(thm)], [c_123803, c_14])).
% 50.75/39.61  tff(c_124592, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_124252, c_124586])).
% 50.75/39.61  tff(c_124603, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_124592])).
% 50.75/39.61  tff(c_123753, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_70])).
% 50.75/39.61  tff(c_68, plain, (![D_66]: (~r2_hidden('#skF_3', D_66) | ~r1_tarski(D_66, '#skF_4') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r1_tarski('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_124447, plain, (![D_1838]: (~r2_hidden('#skF_3', D_1838) | ~r1_tarski(D_1838, '#skF_4') | ~v3_pre_topc(D_1838, '#skF_2') | ~m1_subset_1(D_1838, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_123753, c_68])).
% 50.75/39.61  tff(c_125155, plain, (![A_1876]: (~r2_hidden('#skF_3', A_1876) | ~r1_tarski(A_1876, '#skF_4') | ~v3_pre_topc(A_1876, '#skF_2') | ~r1_tarski(A_1876, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_124447])).
% 50.75/39.61  tff(c_125173, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_124603, c_125155])).
% 50.75/39.61  tff(c_125199, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_124252, c_123752, c_125173])).
% 50.75/39.61  tff(c_125323, plain, (![A_1884, B_1885]: (v3_pre_topc(k1_tops_1(A_1884, B_1885), A_1884) | ~m1_subset_1(B_1885, k1_zfmisc_1(u1_struct_0(A_1884))) | ~l1_pre_topc(A_1884) | ~v2_pre_topc(A_1884))), inference(cnfTransformation, [status(thm)], [f_123])).
% 50.75/39.61  tff(c_125343, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_125323])).
% 50.75/39.61  tff(c_125359, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_125343])).
% 50.75/39.61  tff(c_125361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125199, c_125359])).
% 50.75/39.61  tff(c_125362, plain, (r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 50.75/39.61  tff(c_125399, plain, (![C_1896, B_1897, A_1898]: (r2_hidden(C_1896, B_1897) | ~r2_hidden(C_1896, A_1898) | ~r1_tarski(A_1898, B_1897))), inference(cnfTransformation, [status(thm)], [f_32])).
% 50.75/39.61  tff(c_125406, plain, (![B_1899]: (r2_hidden('#skF_3', B_1899) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), B_1899))), inference(resolution, [status(thm)], [c_125362, c_125399])).
% 50.75/39.61  tff(c_125415, plain, (r2_hidden('#skF_3', u1_struct_0('#skF_2')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_125390, c_125406])).
% 50.75/39.61  tff(c_125419, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_125415])).
% 50.75/39.61  tff(c_125690, plain, (![A_1932, B_1933]: (r1_tarski(k1_tops_1(A_1932, B_1933), B_1933) | ~m1_subset_1(B_1933, k1_zfmisc_1(u1_struct_0(A_1932))) | ~l1_pre_topc(A_1932))), inference(cnfTransformation, [status(thm)], [f_139])).
% 50.75/39.61  tff(c_125701, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_125690])).
% 50.75/39.61  tff(c_125707, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_125701])).
% 50.75/39.61  tff(c_125709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125419, c_125707])).
% 50.75/39.61  tff(c_125711, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_125415])).
% 50.75/39.61  tff(c_125392, plain, (![A_1895]: (r1_tarski(A_1895, u1_struct_0('#skF_2')) | ~r1_tarski(A_1895, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_125385])).
% 50.75/39.61  tff(c_125973, plain, (![A_1960, A_1961]: (r1_tarski(A_1960, u1_struct_0('#skF_2')) | ~r1_tarski(A_1960, A_1961) | ~r1_tarski(A_1961, '#skF_4'))), inference(resolution, [status(thm)], [c_125392, c_14])).
% 50.75/39.61  tff(c_125977, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_125711, c_125973])).
% 50.75/39.61  tff(c_125987, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_125977])).
% 50.75/39.61  tff(c_125363, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_66])).
% 50.75/39.61  tff(c_64, plain, (![D_66]: (~r2_hidden('#skF_3', D_66) | ~r1_tarski(D_66, '#skF_4') | ~v3_pre_topc(D_66, '#skF_2') | ~m1_subset_1(D_66, k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 50.75/39.61  tff(c_125900, plain, (![D_1955]: (~r2_hidden('#skF_3', D_1955) | ~r1_tarski(D_1955, '#skF_4') | ~v3_pre_topc(D_1955, '#skF_2') | ~m1_subset_1(D_1955, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_125363, c_64])).
% 50.75/39.61  tff(c_126730, plain, (![A_2000]: (~r2_hidden('#skF_3', A_2000) | ~r1_tarski(A_2000, '#skF_4') | ~v3_pre_topc(A_2000, '#skF_2') | ~r1_tarski(A_2000, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_36, c_125900])).
% 50.75/39.61  tff(c_126756, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_125987, c_126730])).
% 50.75/39.61  tff(c_126785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126520, c_125711, c_125362, c_126756])).
% 50.75/39.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.75/39.61  
% 50.75/39.61  Inference rules
% 50.75/39.61  ----------------------
% 50.75/39.61  #Ref     : 0
% 50.75/39.61  #Sup     : 30548
% 50.75/39.61  #Fact    : 0
% 50.75/39.61  #Define  : 0
% 50.75/39.61  #Split   : 76
% 50.75/39.61  #Chain   : 0
% 50.75/39.61  #Close   : 0
% 50.75/39.61  
% 50.75/39.61  Ordering : KBO
% 50.75/39.61  
% 50.75/39.61  Simplification rules
% 50.75/39.61  ----------------------
% 50.75/39.61  #Subsume      : 3018
% 50.75/39.61  #Demod        : 22393
% 50.75/39.61  #Tautology    : 7455
% 50.75/39.61  #SimpNegUnit  : 141
% 50.75/39.61  #BackRed      : 164
% 50.75/39.61  
% 50.75/39.61  #Partial instantiations: 0
% 50.75/39.61  #Strategies tried      : 1
% 50.75/39.61  
% 50.75/39.61  Timing (in seconds)
% 50.75/39.61  ----------------------
% 50.75/39.62  Preprocessing        : 0.35
% 50.75/39.62  Parsing              : 0.19
% 50.75/39.62  CNF conversion       : 0.03
% 50.75/39.62  Main loop            : 38.43
% 50.75/39.62  Inferencing          : 3.73
% 50.75/39.62  Reduction            : 20.99
% 50.75/39.62  Demodulation         : 18.62
% 50.75/39.62  BG Simplification    : 0.46
% 50.75/39.62  Subsumption          : 10.65
% 50.75/39.62  Abstraction          : 0.66
% 50.75/39.62  MUC search           : 0.00
% 50.75/39.62  Cooper               : 0.00
% 50.75/39.62  Total                : 38.84
% 50.75/39.62  Index Insertion      : 0.00
% 50.75/39.62  Index Deletion       : 0.00
% 50.75/39.62  Index Matching       : 0.00
% 50.75/39.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
