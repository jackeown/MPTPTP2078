%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1787+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:23 EST 2020

% Result     : Theorem 52.57s
% Output     : CNFRefutation 52.57s
% Verified   : 
% Statistics : Number of formulae       :  145 (1078 expanded)
%              Number of leaves         :   42 ( 399 expanded)
%              Depth                    :   27
%              Number of atoms          :  386 (3947 expanded)
%              Number of equality atoms :   46 ( 269 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_subset_1 > k4_subset_1 > k5_tmap_1 > k5_setfam_1 > k3_xboole_0 > k2_xboole_0 > a_2_0_tmap_1 > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(a_2_0_tmap_1,type,(
    a_2_0_tmap_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => r2_hidden(B,k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_tmap_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k5_tmap_1(A,B) = a_2_0_tmap_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tmap_1)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_126,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B))) )
     => ( r2_hidden(A,a_2_0_tmap_1(B,C))
      <=> ? [D,E] :
            ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
            & m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
            & A = k4_subset_1(u1_struct_0(B),D,k9_subset_1(u1_struct_0(B),E,C))
            & r2_hidden(D,u1_pre_topc(B))
            & r2_hidden(E,u1_pre_topc(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_tmap_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_107,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_84,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_82,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_80,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_480,plain,(
    ! [A_110,B_111] :
      ( k5_tmap_1(A_110,B_111) = a_2_0_tmap_1(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_496,plain,
    ( k5_tmap_1('#skF_6','#skF_7') = a_2_0_tmap_1('#skF_6','#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_480])).

tff(c_503,plain,
    ( k5_tmap_1('#skF_6','#skF_7') = a_2_0_tmap_1('#skF_6','#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_496])).

tff(c_504,plain,(
    k5_tmap_1('#skF_6','#skF_7') = a_2_0_tmap_1('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_503])).

tff(c_78,plain,(
    ~ r2_hidden('#skF_7',k5_tmap_1('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_505,plain,(
    ~ r2_hidden('#skF_7',a_2_0_tmap_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_78])).

tff(c_150,plain,(
    ! [A_64] :
      ( m1_subset_1(u1_pre_topc(A_64),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_64))))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_70,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_154,plain,(
    ! [A_64] :
      ( r1_tarski(u1_pre_topc(A_64),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_150,c_70])).

tff(c_76,plain,(
    ! [A_51] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(A_51))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_72,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(A_46,k1_zfmisc_1(B_47))
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_161,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_180,plain,(
    ! [A_73,B_74,A_75] :
      ( m1_subset_1(A_73,B_74)
      | ~ r2_hidden(A_73,A_75)
      | ~ r1_tarski(A_75,B_74) ) ),
    inference(resolution,[status(thm)],[c_72,c_161])).

tff(c_323,plain,(
    ! [B_97,A_98] :
      ( m1_subset_1(k1_xboole_0,B_97)
      | ~ r1_tarski(u1_pre_topc(A_98),B_97)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(resolution,[status(thm)],[c_76,c_180])).

tff(c_327,plain,(
    ! [A_64] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v2_pre_topc(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_154,c_323])).

tff(c_40,plain,(
    ! [A_6] :
      ( r2_hidden(u1_struct_0(A_6),u1_pre_topc(A_6))
      | ~ v2_pre_topc(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_556,plain,(
    ! [A_114,B_115] :
      ( m1_subset_1(u1_struct_0(A_114),B_115)
      | ~ r1_tarski(u1_pre_topc(A_114),B_115)
      | ~ v2_pre_topc(A_114)
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_40,c_180])).

tff(c_560,plain,(
    ! [A_64] :
      ( m1_subset_1(u1_struct_0(A_64),k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ v2_pre_topc(A_64)
      | ~ l1_pre_topc(A_64) ) ),
    inference(resolution,[status(thm)],[c_154,c_556])).

tff(c_131,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_135,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_80,c_131])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5283,plain,(
    ! [A_330,B_331,C_332] :
      ( m1_subset_1('#skF_4'(A_330,B_331,C_332),k1_zfmisc_1(u1_struct_0(B_331)))
      | ~ r2_hidden(A_330,a_2_0_tmap_1(B_331,C_332))
      | ~ m1_subset_1(C_332,k1_zfmisc_1(u1_struct_0(B_331)))
      | ~ l1_pre_topc(B_331)
      | ~ v2_pre_topc(B_331)
      | v2_struct_0(B_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6409,plain,(
    ! [A_375,B_376,C_377] :
      ( r1_tarski('#skF_4'(A_375,B_376,C_377),u1_struct_0(B_376))
      | ~ r2_hidden(A_375,a_2_0_tmap_1(B_376,C_377))
      | ~ m1_subset_1(C_377,k1_zfmisc_1(u1_struct_0(B_376)))
      | ~ l1_pre_topc(B_376)
      | ~ v2_pre_topc(B_376)
      | v2_struct_0(B_376) ) ),
    inference(resolution,[status(thm)],[c_5283,c_70])).

tff(c_66,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_13211,plain,(
    ! [A_642,B_643,C_644] :
      ( k3_xboole_0('#skF_4'(A_642,B_643,C_644),u1_struct_0(B_643)) = '#skF_4'(A_642,B_643,C_644)
      | ~ r2_hidden(A_642,a_2_0_tmap_1(B_643,C_644))
      | ~ m1_subset_1(C_644,k1_zfmisc_1(u1_struct_0(B_643)))
      | ~ l1_pre_topc(B_643)
      | ~ v2_pre_topc(B_643)
      | v2_struct_0(B_643) ) ),
    inference(resolution,[status(thm)],[c_6409,c_66])).

tff(c_13537,plain,(
    ! [A_662,B_663,A_664] :
      ( k3_xboole_0('#skF_4'(A_662,B_663,A_664),u1_struct_0(B_663)) = '#skF_4'(A_662,B_663,A_664)
      | ~ r2_hidden(A_662,a_2_0_tmap_1(B_663,A_664))
      | ~ l1_pre_topc(B_663)
      | ~ v2_pre_topc(B_663)
      | v2_struct_0(B_663)
      | ~ r1_tarski(A_664,u1_struct_0(B_663)) ) ),
    inference(resolution,[status(thm)],[c_72,c_13211])).

tff(c_13743,plain,(
    ! [B_671,A_672,A_673] :
      ( k3_xboole_0(u1_struct_0(B_671),'#skF_4'(A_672,B_671,A_673)) = '#skF_4'(A_672,B_671,A_673)
      | ~ r2_hidden(A_672,a_2_0_tmap_1(B_671,A_673))
      | ~ l1_pre_topc(B_671)
      | ~ v2_pre_topc(B_671)
      | v2_struct_0(B_671)
      | ~ r1_tarski(A_673,u1_struct_0(B_671)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_13537])).

tff(c_60,plain,(
    ! [A_36,B_37,C_38] :
      ( k9_subset_1(A_36,B_37,C_38) = k3_xboole_0(B_37,C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_13086,plain,(
    ! [B_631,B_632,A_633,C_634] :
      ( k9_subset_1(u1_struct_0(B_631),B_632,'#skF_4'(A_633,B_631,C_634)) = k3_xboole_0(B_632,'#skF_4'(A_633,B_631,C_634))
      | ~ r2_hidden(A_633,a_2_0_tmap_1(B_631,C_634))
      | ~ m1_subset_1(C_634,k1_zfmisc_1(u1_struct_0(B_631)))
      | ~ l1_pre_topc(B_631)
      | ~ v2_pre_topc(B_631)
      | v2_struct_0(B_631) ) ),
    inference(resolution,[status(thm)],[c_5283,c_60])).

tff(c_13130,plain,(
    ! [B_632,A_633] :
      ( k9_subset_1(u1_struct_0('#skF_6'),B_632,'#skF_4'(A_633,'#skF_6','#skF_7')) = k3_xboole_0(B_632,'#skF_4'(A_633,'#skF_6','#skF_7'))
      | ~ r2_hidden(A_633,a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_13086])).

tff(c_13153,plain,(
    ! [B_632,A_633] :
      ( k9_subset_1(u1_struct_0('#skF_6'),B_632,'#skF_4'(A_633,'#skF_6','#skF_7')) = k3_xboole_0(B_632,'#skF_4'(A_633,'#skF_6','#skF_7'))
      | ~ r2_hidden(A_633,a_2_0_tmap_1('#skF_6','#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_13130])).

tff(c_13155,plain,(
    ! [B_635,A_636] :
      ( k9_subset_1(u1_struct_0('#skF_6'),B_635,'#skF_4'(A_636,'#skF_6','#skF_7')) = k3_xboole_0(B_635,'#skF_4'(A_636,'#skF_6','#skF_7'))
      | ~ r2_hidden(A_636,a_2_0_tmap_1('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_13153])).

tff(c_46,plain,(
    ! [B_25,D_31,E_32,C_26] :
      ( r2_hidden(k4_subset_1(u1_struct_0(B_25),D_31,k9_subset_1(u1_struct_0(B_25),E_32,C_26)),a_2_0_tmap_1(B_25,C_26))
      | ~ r2_hidden(E_32,u1_pre_topc(B_25))
      | ~ r2_hidden(D_31,u1_pre_topc(B_25))
      | ~ m1_subset_1(E_32,k1_zfmisc_1(u1_struct_0(B_25)))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0(B_25)))
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(B_25)))
      | ~ l1_pre_topc(B_25)
      | ~ v2_pre_topc(B_25)
      | v2_struct_0(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_13161,plain,(
    ! [D_31,B_635,A_636] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_31,k3_xboole_0(B_635,'#skF_4'(A_636,'#skF_6','#skF_7'))),a_2_0_tmap_1('#skF_6','#skF_4'(A_636,'#skF_6','#skF_7')))
      | ~ r2_hidden(B_635,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_31,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_635,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_4'(A_636,'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(A_636,a_2_0_tmap_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13155,c_46])).

tff(c_13174,plain,(
    ! [D_31,B_635,A_636] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_31,k3_xboole_0(B_635,'#skF_4'(A_636,'#skF_6','#skF_7'))),a_2_0_tmap_1('#skF_6','#skF_4'(A_636,'#skF_6','#skF_7')))
      | ~ r2_hidden(B_635,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_31,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_635,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_4'(A_636,'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(A_636,a_2_0_tmap_1('#skF_6','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_13161])).

tff(c_13175,plain,(
    ! [D_31,B_635,A_636] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_31,k3_xboole_0(B_635,'#skF_4'(A_636,'#skF_6','#skF_7'))),a_2_0_tmap_1('#skF_6','#skF_4'(A_636,'#skF_6','#skF_7')))
      | ~ r2_hidden(B_635,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_31,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_635,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_4'(A_636,'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_636,a_2_0_tmap_1('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_13174])).

tff(c_13750,plain,(
    ! [D_31,A_672] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_31,'#skF_4'(A_672,'#skF_6','#skF_7')),a_2_0_tmap_1('#skF_6','#skF_4'(A_672,'#skF_6','#skF_7')))
      | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_31,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_4'(A_672,'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_672,a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(A_672,a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski('#skF_7',u1_struct_0('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13743,c_13175])).

tff(c_13795,plain,(
    ! [D_31,A_672] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_31,'#skF_4'(A_672,'#skF_6','#skF_7')),a_2_0_tmap_1('#skF_6','#skF_4'(A_672,'#skF_6','#skF_7')))
      | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_31,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_4'(A_672,'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_672,a_2_0_tmap_1('#skF_6','#skF_7'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_84,c_82,c_13750])).

tff(c_13796,plain,(
    ! [D_31,A_672] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_31,'#skF_4'(A_672,'#skF_6','#skF_7')),a_2_0_tmap_1('#skF_6','#skF_4'(A_672,'#skF_6','#skF_7')))
      | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_31,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_31,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_4'(A_672,'#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ r2_hidden(A_672,a_2_0_tmap_1('#skF_6','#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_13795])).

tff(c_14267,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_13796])).

tff(c_14276,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_560,c_14267])).

tff(c_14295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_14276])).

tff(c_14297,plain,(
    m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_13796])).

tff(c_14972,plain,(
    ! [B_699] : k9_subset_1(u1_struct_0('#skF_6'),B_699,u1_struct_0('#skF_6')) = k3_xboole_0(B_699,u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_14297,c_60])).

tff(c_36,plain,(
    ! [A_6,B_16,C_18] :
      ( r2_hidden(k9_subset_1(u1_struct_0(A_6),B_16,C_18),u1_pre_topc(A_6))
      | ~ r2_hidden(C_18,u1_pre_topc(A_6))
      | ~ r2_hidden(B_16,u1_pre_topc(A_6))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ v2_pre_topc(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14985,plain,(
    ! [B_699] :
      ( r2_hidden(k3_xboole_0(B_699,u1_struct_0('#skF_6')),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(B_699,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_699,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ v2_pre_topc('#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14972,c_36])).

tff(c_15011,plain,(
    ! [B_699] :
      ( r2_hidden(k3_xboole_0(B_699,u1_struct_0('#skF_6')),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(B_699,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_699,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_14297,c_14985])).

tff(c_25732,plain,(
    ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_15011])).

tff(c_25735,plain,
    ( ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_25732])).

tff(c_25739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_25735])).

tff(c_25924,plain,(
    ! [B_786] :
      ( r2_hidden(k3_xboole_0(B_786,u1_struct_0('#skF_6')),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(B_786,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_786,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(splitRight,[status(thm)],[c_15011])).

tff(c_44,plain,(
    ! [A_23] :
      ( m1_subset_1(u1_pre_topc(A_23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23))))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_168,plain,(
    ! [A_67,A_23] :
      ( m1_subset_1(A_67,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ r2_hidden(A_67,u1_pre_topc(A_23))
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_498,plain,(
    ! [A_23,A_67] :
      ( k5_tmap_1(A_23,A_67) = a_2_0_tmap_1(A_23,A_67)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23)
      | ~ r2_hidden(A_67,u1_pre_topc(A_23))
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_168,c_480])).

tff(c_25949,plain,(
    ! [B_786] :
      ( k5_tmap_1('#skF_6',k3_xboole_0(B_786,u1_struct_0('#skF_6'))) = a_2_0_tmap_1('#skF_6',k3_xboole_0(B_786,u1_struct_0('#skF_6')))
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ r2_hidden(B_786,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_786,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_25924,c_498])).

tff(c_26041,plain,(
    ! [B_786] :
      ( k5_tmap_1('#skF_6',k3_xboole_0(B_786,u1_struct_0('#skF_6'))) = a_2_0_tmap_1('#skF_6',k3_xboole_0(B_786,u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | ~ r2_hidden(B_786,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_786,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_25949])).

tff(c_26381,plain,(
    ! [B_789] :
      ( k5_tmap_1('#skF_6',k3_xboole_0(B_789,u1_struct_0('#skF_6'))) = a_2_0_tmap_1('#skF_6',k3_xboole_0(B_789,u1_struct_0('#skF_6')))
      | ~ r2_hidden(B_789,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_789,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_26041])).

tff(c_26452,plain,
    ( k5_tmap_1('#skF_6',k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_6'))) = a_2_0_tmap_1('#skF_6',k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_6')))
    | ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_6'))
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_327,c_26381])).

tff(c_26522,plain,
    ( k5_tmap_1('#skF_6',k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_6'))) = a_2_0_tmap_1('#skF_6',k3_xboole_0(k1_xboole_0,u1_struct_0('#skF_6')))
    | ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_26452])).

tff(c_26684,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_26522])).

tff(c_26687,plain,
    ( ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_26684])).

tff(c_26691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_26687])).

tff(c_26693,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_26522])).

tff(c_169,plain,(
    ! [A_67,B_47,A_46] :
      ( m1_subset_1(A_67,B_47)
      | ~ r2_hidden(A_67,A_46)
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_72,c_161])).

tff(c_26903,plain,(
    ! [B_791] :
      ( m1_subset_1(k1_xboole_0,B_791)
      | ~ r1_tarski(u1_pre_topc('#skF_6'),B_791) ) ),
    inference(resolution,[status(thm)],[c_26693,c_169])).

tff(c_26907,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6')))
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_154,c_26903])).

tff(c_26910,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_26907])).

tff(c_344,plain,(
    ! [A_102] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ v2_pre_topc(A_102)
      | ~ l1_pre_topc(A_102) ) ),
    inference(resolution,[status(thm)],[c_154,c_323])).

tff(c_223,plain,(
    ! [A_83,B_84,C_85] :
      ( k4_subset_1(A_83,B_84,C_85) = k2_xboole_0(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_235,plain,(
    ! [B_84] :
      ( k4_subset_1(u1_struct_0('#skF_6'),B_84,'#skF_7') = k2_xboole_0(B_84,'#skF_7')
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_223])).

tff(c_350,plain,
    ( k4_subset_1(u1_struct_0('#skF_6'),k1_xboole_0,'#skF_7') = k2_xboole_0(k1_xboole_0,'#skF_7')
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_344,c_235])).

tff(c_363,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),k1_xboole_0,'#skF_7') = k2_xboole_0(k1_xboole_0,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_350])).

tff(c_328,plain,(
    ! [A_99,C_100,B_101] :
      ( k4_subset_1(A_99,C_100,B_101) = k4_subset_1(A_99,B_101,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_382,plain,(
    ! [B_104] :
      ( k4_subset_1(u1_struct_0('#skF_6'),B_104,'#skF_7') = k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_80,c_328])).

tff(c_386,plain,
    ( k4_subset_1(u1_struct_0('#skF_6'),k1_xboole_0,'#skF_7') = k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_xboole_0)
    | ~ v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_327,c_382])).

tff(c_404,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_xboole_0) = k2_xboole_0(k1_xboole_0,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84,c_363,c_386])).

tff(c_62,plain,(
    ! [A_39] : k2_xboole_0(A_39,k1_xboole_0) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_247,plain,(
    ! [A_89,A_90] :
      ( m1_subset_1(A_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ r2_hidden(A_89,u1_pre_topc(A_90))
      | ~ l1_pre_topc(A_90) ) ),
    inference(resolution,[status(thm)],[c_44,c_161])).

tff(c_261,plain,(
    ! [A_91,A_92] :
      ( r1_tarski(A_91,u1_struct_0(A_92))
      | ~ r2_hidden(A_91,u1_pre_topc(A_92))
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_247,c_70])).

tff(c_269,plain,(
    ! [A_51] :
      ( r1_tarski(k1_xboole_0,u1_struct_0(A_51))
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(resolution,[status(thm)],[c_76,c_261])).

tff(c_712,plain,(
    ! [B_136,B_137,A_138] :
      ( k4_subset_1(B_136,B_137,A_138) = k2_xboole_0(B_137,A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(B_136))
      | ~ r1_tarski(A_138,B_136) ) ),
    inference(resolution,[status(thm)],[c_72,c_223])).

tff(c_734,plain,(
    ! [A_139] :
      ( k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',A_139) = k2_xboole_0('#skF_7',A_139)
      | ~ r1_tarski(A_139,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_80,c_712])).

tff(c_742,plain,
    ( k4_subset_1(u1_struct_0('#skF_6'),'#skF_7',k1_xboole_0) = k2_xboole_0('#skF_7',k1_xboole_0)
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_269,c_734])).

tff(c_755,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_404,c_62,c_742])).

tff(c_762,plain,(
    k4_subset_1(u1_struct_0('#skF_6'),k1_xboole_0,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_363])).

tff(c_25741,plain,(
    r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_15011])).

tff(c_139,plain,(
    k3_xboole_0('#skF_7',u1_struct_0('#skF_6')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_135,c_66])).

tff(c_201,plain,(
    ! [A_79,B_80,C_81] :
      ( k9_subset_1(A_79,B_80,C_81) = k3_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_213,plain,(
    ! [B_80] : k9_subset_1(u1_struct_0('#skF_6'),B_80,'#skF_7') = k3_xboole_0(B_80,'#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_201])).

tff(c_6929,plain,(
    ! [B_398,D_399,E_400,C_401] :
      ( r2_hidden(k4_subset_1(u1_struct_0(B_398),D_399,k9_subset_1(u1_struct_0(B_398),E_400,C_401)),a_2_0_tmap_1(B_398,C_401))
      | ~ r2_hidden(E_400,u1_pre_topc(B_398))
      | ~ r2_hidden(D_399,u1_pre_topc(B_398))
      | ~ m1_subset_1(E_400,k1_zfmisc_1(u1_struct_0(B_398)))
      | ~ m1_subset_1(D_399,k1_zfmisc_1(u1_struct_0(B_398)))
      | ~ m1_subset_1(C_401,k1_zfmisc_1(u1_struct_0(B_398)))
      | ~ l1_pre_topc(B_398)
      | ~ v2_pre_topc(B_398)
      | v2_struct_0(B_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6975,plain,(
    ! [D_399,B_80] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_399,k3_xboole_0(B_80,'#skF_7')),a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(B_80,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_399,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_399,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_6929])).

tff(c_6983,plain,(
    ! [D_399,B_80] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_399,k3_xboole_0(B_80,'#skF_7')),a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(B_80,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_399,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_399,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_6975])).

tff(c_7050,plain,(
    ! [D_404,B_405] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_404,k3_xboole_0(B_405,'#skF_7')),a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(B_405,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_404,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_405,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_404,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6983])).

tff(c_170118,plain,(
    ! [D_2034,B_2035] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_2034,k3_xboole_0('#skF_7',B_2035)),a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(B_2035,u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_2034,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(B_2035,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_2034,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_7050])).

tff(c_170381,plain,(
    ! [D_2034] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_2034,'#skF_7'),a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6'))
      | ~ r2_hidden(D_2034,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(u1_struct_0('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(D_2034,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_170118])).

tff(c_170486,plain,(
    ! [D_2036] :
      ( r2_hidden(k4_subset_1(u1_struct_0('#skF_6'),D_2036,'#skF_7'),a_2_0_tmap_1('#skF_6','#skF_7'))
      | ~ r2_hidden(D_2036,u1_pre_topc('#skF_6'))
      | ~ m1_subset_1(D_2036,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14297,c_25741,c_170381])).

tff(c_170864,plain,
    ( r2_hidden('#skF_7',a_2_0_tmap_1('#skF_6','#skF_7'))
    | ~ r2_hidden(k1_xboole_0,u1_pre_topc('#skF_6'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_170486])).

tff(c_170972,plain,(
    r2_hidden('#skF_7',a_2_0_tmap_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26910,c_26693,c_170864])).

tff(c_170974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_505,c_170972])).

%------------------------------------------------------------------------------
