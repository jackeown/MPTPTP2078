%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:58 EST 2020

% Result     : Theorem 7.13s
% Output     : CNFRefutation 7.40s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 261 expanded)
%              Number of leaves         :   45 ( 110 expanded)
%              Depth                    :   14
%              Number of atoms          :  229 ( 855 expanded)
%              Number of equality atoms :   15 (  57 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(v1_yellow_0,type,(
    v1_yellow_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_132,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_yellow_0(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v2_waybel_0(B,A)
              & v13_waybel_0(B,A)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v1_subset_1(B,u1_struct_0(A))
            <=> ~ r2_hidden(k3_yellow_0(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( l1_orders_2(A)
     => m1_subset_1(k1_yellow_0(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_yellow_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_yellow_0(A)
        & l1_orders_2(A) )
     => ( r1_yellow_0(A,k1_xboole_0)
        & r2_yellow_0(A,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v13_waybel_0(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r2_hidden(C,B)
                        & r1_orders_2(A,C,D) )
                     => r2_hidden(D,B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_107,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(A_71,k1_zfmisc_1(B_72))
      | ~ r1_tarski(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [B_62] :
      ( ~ v1_subset_1(B_62,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_114,plain,(
    ! [B_72] :
      ( ~ v1_subset_1(B_72,B_72)
      | ~ r1_tarski(B_72,B_72) ) ),
    inference(resolution,[status(thm)],[c_107,c_60])).

tff(c_118,plain,(
    ! [B_72] : ~ v1_subset_1(B_72,B_72) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_114])).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_102,plain,(
    ! [A_69,B_70] :
      ( r1_tarski(A_69,B_70)
      | ~ m1_subset_1(A_69,k1_zfmisc_1(B_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_102])).

tff(c_283,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_288,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_106,c_283])).

tff(c_293,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_288])).

tff(c_70,plain,(
    l1_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_272,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_1'(A_100,B_101),A_100)
      | r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_282,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1('#skF_1'(A_100,B_101),A_100)
      | r1_tarski(A_100,B_101) ) ),
    inference(resolution,[status(thm)],[c_272,c_14])).

tff(c_413,plain,(
    ! [A_125,B_126] :
      ( r2_lattice3(A_125,k1_xboole_0,B_126)
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_435,plain,(
    ! [A_125,B_101] :
      ( r2_lattice3(A_125,k1_xboole_0,'#skF_1'(u1_struct_0(A_125),B_101))
      | ~ l1_orders_2(A_125)
      | r1_tarski(u1_struct_0(A_125),B_101) ) ),
    inference(resolution,[status(thm)],[c_282,c_413])).

tff(c_64,plain,(
    v13_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_82,plain,
    ( r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
    | ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_120,plain,(
    ~ v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_180,plain,(
    ! [B_89,A_90] :
      ( v1_subset_1(B_89,A_90)
      | B_89 = A_90
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_190,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_62,c_180])).

tff(c_195,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_190])).

tff(c_139,plain,(
    ! [B_80,A_81] :
      ( B_80 = A_81
      | ~ r1_tarski(B_80,A_81)
      | ~ r1_tarski(A_81,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,
    ( u1_struct_0('#skF_5') = '#skF_6'
    | ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_106,c_139])).

tff(c_149,plain,(
    ~ r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_196,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_149])).

tff(c_203,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_196])).

tff(c_204,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_92,plain,(
    ! [A_67] :
      ( k1_yellow_0(A_67,k1_xboole_0) = k3_yellow_0(A_67)
      | ~ l1_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_96,plain,(
    k1_yellow_0('#skF_5',k1_xboole_0) = k3_yellow_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_92])).

tff(c_121,plain,(
    ! [A_74,B_75] :
      ( m1_subset_1(k1_yellow_0(A_74,B_75),u1_struct_0(A_74))
      | ~ l1_orders_2(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_121])).

tff(c_126,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_124])).

tff(c_207,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_126])).

tff(c_231,plain,(
    ! [A_92,B_93] :
      ( r2_hidden(A_92,B_93)
      | v1_xboole_0(B_93)
      | ~ m1_subset_1(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_88,plain,
    ( v1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_206,plain,(
    ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_88])).

tff(c_234,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_231,c_206])).

tff(c_244,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_234])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_244])).

tff(c_247,plain,(
    r2_hidden(k3_yellow_0('#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_74,plain,(
    v5_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_72,plain,(
    v1_yellow_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_40,plain,(
    ! [A_32] :
      ( r1_yellow_0(A_32,k1_xboole_0)
      | ~ l1_orders_2(A_32)
      | ~ v1_yellow_0(A_32)
      | ~ v5_orders_2(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_253,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k1_yellow_0(A_94,B_95),u1_struct_0(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_256,plain,
    ( m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
    | ~ l1_orders_2('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_253])).

tff(c_258,plain,(
    m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_256])).

tff(c_1613,plain,(
    ! [A_299,B_300,D_301] :
      ( r1_orders_2(A_299,k1_yellow_0(A_299,B_300),D_301)
      | ~ r2_lattice3(A_299,B_300,D_301)
      | ~ m1_subset_1(D_301,u1_struct_0(A_299))
      | ~ r1_yellow_0(A_299,B_300)
      | ~ m1_subset_1(k1_yellow_0(A_299,B_300),u1_struct_0(A_299))
      | ~ l1_orders_2(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1623,plain,(
    ! [D_301] :
      ( r1_orders_2('#skF_5',k1_yellow_0('#skF_5',k1_xboole_0),D_301)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_301)
      | ~ m1_subset_1(D_301,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ m1_subset_1(k3_yellow_0('#skF_5'),u1_struct_0('#skF_5'))
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_1613])).

tff(c_1632,plain,(
    ! [D_301] :
      ( r1_orders_2('#skF_5',k3_yellow_0('#skF_5'),D_301)
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_301)
      | ~ m1_subset_1(D_301,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_258,c_96,c_1623])).

tff(c_1671,plain,(
    ~ r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1632])).

tff(c_1674,plain,
    ( ~ l1_orders_2('#skF_5')
    | ~ v1_yellow_0('#skF_5')
    | ~ v5_orders_2('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_1671])).

tff(c_1677,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1674])).

tff(c_1679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1677])).

tff(c_1681,plain,(
    r1_yellow_0('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1632])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k1_yellow_0(A_30,B_31),u1_struct_0(A_30))
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2021,plain,(
    ! [A_354,B_355,D_356] :
      ( r1_orders_2(A_354,k1_yellow_0(A_354,B_355),D_356)
      | ~ r2_lattice3(A_354,B_355,D_356)
      | ~ m1_subset_1(D_356,u1_struct_0(A_354))
      | ~ r1_yellow_0(A_354,B_355)
      | ~ l1_orders_2(A_354) ) ),
    inference(resolution,[status(thm)],[c_36,c_1613])).

tff(c_46,plain,(
    ! [D_59,B_50,A_36,C_57] :
      ( r2_hidden(D_59,B_50)
      | ~ r1_orders_2(A_36,C_57,D_59)
      | ~ r2_hidden(C_57,B_50)
      | ~ m1_subset_1(D_59,u1_struct_0(A_36))
      | ~ m1_subset_1(C_57,u1_struct_0(A_36))
      | ~ v13_waybel_0(B_50,A_36)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_orders_2(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3912,plain,(
    ! [D_516,B_517,A_518,B_519] :
      ( r2_hidden(D_516,B_517)
      | ~ r2_hidden(k1_yellow_0(A_518,B_519),B_517)
      | ~ m1_subset_1(k1_yellow_0(A_518,B_519),u1_struct_0(A_518))
      | ~ v13_waybel_0(B_517,A_518)
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0(A_518)))
      | ~ r2_lattice3(A_518,B_519,D_516)
      | ~ m1_subset_1(D_516,u1_struct_0(A_518))
      | ~ r1_yellow_0(A_518,B_519)
      | ~ l1_orders_2(A_518) ) ),
    inference(resolution,[status(thm)],[c_2021,c_46])).

tff(c_3924,plain,(
    ! [D_516,B_517] :
      ( r2_hidden(D_516,B_517)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_517)
      | ~ m1_subset_1(k1_yellow_0('#skF_5',k1_xboole_0),u1_struct_0('#skF_5'))
      | ~ v13_waybel_0(B_517,'#skF_5')
      | ~ m1_subset_1(B_517,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_516)
      | ~ m1_subset_1(D_516,u1_struct_0('#skF_5'))
      | ~ r1_yellow_0('#skF_5',k1_xboole_0)
      | ~ l1_orders_2('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_3912])).

tff(c_4201,plain,(
    ! [D_539,B_540] :
      ( r2_hidden(D_539,B_540)
      | ~ r2_hidden(k3_yellow_0('#skF_5'),B_540)
      | ~ v13_waybel_0(B_540,'#skF_5')
      | ~ m1_subset_1(B_540,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_539)
      | ~ m1_subset_1(D_539,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1681,c_258,c_96,c_3924])).

tff(c_4235,plain,(
    ! [D_539] :
      ( r2_hidden(D_539,'#skF_6')
      | ~ r2_hidden(k3_yellow_0('#skF_5'),'#skF_6')
      | ~ v13_waybel_0('#skF_6','#skF_5')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_539)
      | ~ m1_subset_1(D_539,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_62,c_4201])).

tff(c_4252,plain,(
    ! [D_541] :
      ( r2_hidden(D_541,'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,D_541)
      | ~ m1_subset_1(D_541,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_247,c_4235])).

tff(c_4734,plain,(
    ! [B_553] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_553),'#skF_6')
      | ~ r2_lattice3('#skF_5',k1_xboole_0,'#skF_1'(u1_struct_0('#skF_5'),B_553))
      | r1_tarski(u1_struct_0('#skF_5'),B_553) ) ),
    inference(resolution,[status(thm)],[c_282,c_4252])).

tff(c_4746,plain,(
    ! [B_101] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_101),'#skF_6')
      | ~ l1_orders_2('#skF_5')
      | r1_tarski(u1_struct_0('#skF_5'),B_101) ) ),
    inference(resolution,[status(thm)],[c_435,c_4734])).

tff(c_5278,plain,(
    ! [B_579] :
      ( r2_hidden('#skF_1'(u1_struct_0('#skF_5'),B_579),'#skF_6')
      | r1_tarski(u1_struct_0('#skF_5'),B_579) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4746])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5290,plain,(
    r1_tarski(u1_struct_0('#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5278,c_4])).

tff(c_5301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_293,c_5290])).

tff(c_5302,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_288])).

tff(c_248,plain,(
    v1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_5305,plain,(
    v1_subset_1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5302,c_248])).

tff(c_5310,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_5305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:28:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.13/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.54  
% 7.40/2.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.54  %$ r2_lattice3 > r1_orders_2 > r1_lattice3 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_yellow_0 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_yellow_0 > v1_xboole_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > k3_yellow_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 7.40/2.54  
% 7.40/2.54  %Foreground sorts:
% 7.40/2.54  
% 7.40/2.54  
% 7.40/2.54  %Background operators:
% 7.40/2.54  
% 7.40/2.54  
% 7.40/2.54  %Foreground operators:
% 7.40/2.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.40/2.54  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 7.40/2.54  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 7.40/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.40/2.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.40/2.54  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 7.40/2.54  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 7.40/2.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.40/2.54  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 7.40/2.54  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 7.40/2.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.40/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.40/2.54  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 7.40/2.54  tff('#skF_5', type, '#skF_5': $i).
% 7.40/2.54  tff('#skF_6', type, '#skF_6': $i).
% 7.40/2.54  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 7.40/2.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.40/2.54  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 7.40/2.54  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.40/2.54  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 7.40/2.54  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 7.40/2.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.40/2.54  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 7.40/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.40/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.40/2.54  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 7.40/2.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.40/2.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.40/2.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.40/2.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.40/2.54  tff(v1_yellow_0, type, v1_yellow_0: $i > $o).
% 7.40/2.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.40/2.54  
% 7.40/2.56  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.40/2.56  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.40/2.56  tff(f_132, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 7.40/2.56  tff(f_161, negated_conjecture, ~(![A]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, A)) & v13_waybel_0(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_subset_1(B, u1_struct_0(A)) <=> ~r2_hidden(k3_yellow_0(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 7.40/2.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.40/2.56  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.40/2.56  tff(f_106, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 7.40/2.56  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 7.40/2.56  tff(f_84, axiom, (![A, B]: (l1_orders_2(A) => m1_subset_1(k1_yellow_0(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_yellow_0)).
% 7.40/2.56  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 7.40/2.56  tff(f_97, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_yellow_0(A)) & l1_orders_2(A)) => (r1_yellow_0(A, k1_xboole_0) & r2_yellow_0(A, u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 7.40/2.56  tff(f_80, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_yellow_0)).
% 7.40/2.56  tff(f_125, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v13_waybel_0(B, A) <=> (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r2_hidden(C, B) & r1_orders_2(A, C, D)) => r2_hidden(D, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 7.40/2.56  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.56  tff(c_107, plain, (![A_71, B_72]: (m1_subset_1(A_71, k1_zfmisc_1(B_72)) | ~r1_tarski(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.40/2.56  tff(c_60, plain, (![B_62]: (~v1_subset_1(B_62, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(B_62)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.56  tff(c_114, plain, (![B_72]: (~v1_subset_1(B_72, B_72) | ~r1_tarski(B_72, B_72))), inference(resolution, [status(thm)], [c_107, c_60])).
% 7.40/2.56  tff(c_118, plain, (![B_72]: (~v1_subset_1(B_72, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_114])).
% 7.40/2.56  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_102, plain, (![A_69, B_70]: (r1_tarski(A_69, B_70) | ~m1_subset_1(A_69, k1_zfmisc_1(B_70)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.40/2.56  tff(c_106, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_62, c_102])).
% 7.40/2.56  tff(c_283, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.56  tff(c_288, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_106, c_283])).
% 7.40/2.56  tff(c_293, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_288])).
% 7.40/2.56  tff(c_70, plain, (l1_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_272, plain, (![A_100, B_101]: (r2_hidden('#skF_1'(A_100, B_101), A_100) | r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.40/2.56  tff(c_14, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.40/2.56  tff(c_282, plain, (![A_100, B_101]: (m1_subset_1('#skF_1'(A_100, B_101), A_100) | r1_tarski(A_100, B_101))), inference(resolution, [status(thm)], [c_272, c_14])).
% 7.40/2.56  tff(c_413, plain, (![A_125, B_126]: (r2_lattice3(A_125, k1_xboole_0, B_126) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.40/2.56  tff(c_435, plain, (![A_125, B_101]: (r2_lattice3(A_125, k1_xboole_0, '#skF_1'(u1_struct_0(A_125), B_101)) | ~l1_orders_2(A_125) | r1_tarski(u1_struct_0(A_125), B_101))), inference(resolution, [status(thm)], [c_282, c_413])).
% 7.40/2.56  tff(c_64, plain, (v13_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_68, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_82, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_120, plain, (~v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_82])).
% 7.40/2.56  tff(c_180, plain, (![B_89, A_90]: (v1_subset_1(B_89, A_90) | B_89=A_90 | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.40/2.56  tff(c_190, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_62, c_180])).
% 7.40/2.56  tff(c_195, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_120, c_190])).
% 7.40/2.56  tff(c_139, plain, (![B_80, A_81]: (B_80=A_81 | ~r1_tarski(B_80, A_81) | ~r1_tarski(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.40/2.56  tff(c_144, plain, (u1_struct_0('#skF_5')='#skF_6' | ~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_106, c_139])).
% 7.40/2.56  tff(c_149, plain, (~r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_144])).
% 7.40/2.56  tff(c_196, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_195, c_149])).
% 7.40/2.56  tff(c_203, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_196])).
% 7.40/2.56  tff(c_204, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_144])).
% 7.40/2.56  tff(c_92, plain, (![A_67]: (k1_yellow_0(A_67, k1_xboole_0)=k3_yellow_0(A_67) | ~l1_orders_2(A_67))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.40/2.56  tff(c_96, plain, (k1_yellow_0('#skF_5', k1_xboole_0)=k3_yellow_0('#skF_5')), inference(resolution, [status(thm)], [c_70, c_92])).
% 7.40/2.56  tff(c_121, plain, (![A_74, B_75]: (m1_subset_1(k1_yellow_0(A_74, B_75), u1_struct_0(A_74)) | ~l1_orders_2(A_74))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.40/2.56  tff(c_124, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_96, c_121])).
% 7.40/2.56  tff(c_126, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_124])).
% 7.40/2.56  tff(c_207, plain, (m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_126])).
% 7.40/2.56  tff(c_231, plain, (![A_92, B_93]: (r2_hidden(A_92, B_93) | v1_xboole_0(B_93) | ~m1_subset_1(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.40/2.56  tff(c_88, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_206, plain, (~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_120, c_88])).
% 7.40/2.56  tff(c_234, plain, (v1_xboole_0('#skF_6') | ~m1_subset_1(k3_yellow_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_231, c_206])).
% 7.40/2.56  tff(c_244, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_234])).
% 7.40/2.56  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_244])).
% 7.40/2.56  tff(c_247, plain, (r2_hidden(k3_yellow_0('#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_82])).
% 7.40/2.56  tff(c_80, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_74, plain, (v5_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_72, plain, (v1_yellow_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 7.40/2.56  tff(c_40, plain, (![A_32]: (r1_yellow_0(A_32, k1_xboole_0) | ~l1_orders_2(A_32) | ~v1_yellow_0(A_32) | ~v5_orders_2(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.40/2.56  tff(c_253, plain, (![A_94, B_95]: (m1_subset_1(k1_yellow_0(A_94, B_95), u1_struct_0(A_94)) | ~l1_orders_2(A_94))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.40/2.56  tff(c_256, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_96, c_253])).
% 7.40/2.56  tff(c_258, plain, (m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_256])).
% 7.40/2.56  tff(c_1613, plain, (![A_299, B_300, D_301]: (r1_orders_2(A_299, k1_yellow_0(A_299, B_300), D_301) | ~r2_lattice3(A_299, B_300, D_301) | ~m1_subset_1(D_301, u1_struct_0(A_299)) | ~r1_yellow_0(A_299, B_300) | ~m1_subset_1(k1_yellow_0(A_299, B_300), u1_struct_0(A_299)) | ~l1_orders_2(A_299))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.40/2.56  tff(c_1623, plain, (![D_301]: (r1_orders_2('#skF_5', k1_yellow_0('#skF_5', k1_xboole_0), D_301) | ~r2_lattice3('#skF_5', k1_xboole_0, D_301) | ~m1_subset_1(D_301, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~m1_subset_1(k3_yellow_0('#skF_5'), u1_struct_0('#skF_5')) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_1613])).
% 7.40/2.56  tff(c_1632, plain, (![D_301]: (r1_orders_2('#skF_5', k3_yellow_0('#skF_5'), D_301) | ~r2_lattice3('#skF_5', k1_xboole_0, D_301) | ~m1_subset_1(D_301, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_258, c_96, c_1623])).
% 7.40/2.56  tff(c_1671, plain, (~r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1632])).
% 7.40/2.56  tff(c_1674, plain, (~l1_orders_2('#skF_5') | ~v1_yellow_0('#skF_5') | ~v5_orders_2('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_1671])).
% 7.40/2.56  tff(c_1677, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1674])).
% 7.40/2.56  tff(c_1679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_1677])).
% 7.40/2.56  tff(c_1681, plain, (r1_yellow_0('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1632])).
% 7.40/2.56  tff(c_36, plain, (![A_30, B_31]: (m1_subset_1(k1_yellow_0(A_30, B_31), u1_struct_0(A_30)) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.40/2.56  tff(c_2021, plain, (![A_354, B_355, D_356]: (r1_orders_2(A_354, k1_yellow_0(A_354, B_355), D_356) | ~r2_lattice3(A_354, B_355, D_356) | ~m1_subset_1(D_356, u1_struct_0(A_354)) | ~r1_yellow_0(A_354, B_355) | ~l1_orders_2(A_354))), inference(resolution, [status(thm)], [c_36, c_1613])).
% 7.40/2.56  tff(c_46, plain, (![D_59, B_50, A_36, C_57]: (r2_hidden(D_59, B_50) | ~r1_orders_2(A_36, C_57, D_59) | ~r2_hidden(C_57, B_50) | ~m1_subset_1(D_59, u1_struct_0(A_36)) | ~m1_subset_1(C_57, u1_struct_0(A_36)) | ~v13_waybel_0(B_50, A_36) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_orders_2(A_36))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.40/2.56  tff(c_3912, plain, (![D_516, B_517, A_518, B_519]: (r2_hidden(D_516, B_517) | ~r2_hidden(k1_yellow_0(A_518, B_519), B_517) | ~m1_subset_1(k1_yellow_0(A_518, B_519), u1_struct_0(A_518)) | ~v13_waybel_0(B_517, A_518) | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0(A_518))) | ~r2_lattice3(A_518, B_519, D_516) | ~m1_subset_1(D_516, u1_struct_0(A_518)) | ~r1_yellow_0(A_518, B_519) | ~l1_orders_2(A_518))), inference(resolution, [status(thm)], [c_2021, c_46])).
% 7.40/2.56  tff(c_3924, plain, (![D_516, B_517]: (r2_hidden(D_516, B_517) | ~r2_hidden(k3_yellow_0('#skF_5'), B_517) | ~m1_subset_1(k1_yellow_0('#skF_5', k1_xboole_0), u1_struct_0('#skF_5')) | ~v13_waybel_0(B_517, '#skF_5') | ~m1_subset_1(B_517, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_lattice3('#skF_5', k1_xboole_0, D_516) | ~m1_subset_1(D_516, u1_struct_0('#skF_5')) | ~r1_yellow_0('#skF_5', k1_xboole_0) | ~l1_orders_2('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_96, c_3912])).
% 7.40/2.56  tff(c_4201, plain, (![D_539, B_540]: (r2_hidden(D_539, B_540) | ~r2_hidden(k3_yellow_0('#skF_5'), B_540) | ~v13_waybel_0(B_540, '#skF_5') | ~m1_subset_1(B_540, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_lattice3('#skF_5', k1_xboole_0, D_539) | ~m1_subset_1(D_539, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1681, c_258, c_96, c_3924])).
% 7.40/2.56  tff(c_4235, plain, (![D_539]: (r2_hidden(D_539, '#skF_6') | ~r2_hidden(k3_yellow_0('#skF_5'), '#skF_6') | ~v13_waybel_0('#skF_6', '#skF_5') | ~r2_lattice3('#skF_5', k1_xboole_0, D_539) | ~m1_subset_1(D_539, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_62, c_4201])).
% 7.40/2.56  tff(c_4252, plain, (![D_541]: (r2_hidden(D_541, '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, D_541) | ~m1_subset_1(D_541, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_247, c_4235])).
% 7.40/2.56  tff(c_4734, plain, (![B_553]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_553), '#skF_6') | ~r2_lattice3('#skF_5', k1_xboole_0, '#skF_1'(u1_struct_0('#skF_5'), B_553)) | r1_tarski(u1_struct_0('#skF_5'), B_553))), inference(resolution, [status(thm)], [c_282, c_4252])).
% 7.40/2.56  tff(c_4746, plain, (![B_101]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_101), '#skF_6') | ~l1_orders_2('#skF_5') | r1_tarski(u1_struct_0('#skF_5'), B_101))), inference(resolution, [status(thm)], [c_435, c_4734])).
% 7.40/2.56  tff(c_5278, plain, (![B_579]: (r2_hidden('#skF_1'(u1_struct_0('#skF_5'), B_579), '#skF_6') | r1_tarski(u1_struct_0('#skF_5'), B_579))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4746])).
% 7.40/2.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.40/2.56  tff(c_5290, plain, (r1_tarski(u1_struct_0('#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_5278, c_4])).
% 7.40/2.56  tff(c_5301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_293, c_5290])).
% 7.40/2.56  tff(c_5302, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_288])).
% 7.40/2.56  tff(c_248, plain, (v1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_82])).
% 7.40/2.56  tff(c_5305, plain, (v1_subset_1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5302, c_248])).
% 7.40/2.56  tff(c_5310, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_5305])).
% 7.40/2.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.40/2.56  
% 7.40/2.56  Inference rules
% 7.40/2.56  ----------------------
% 7.40/2.56  #Ref     : 0
% 7.40/2.56  #Sup     : 1184
% 7.40/2.56  #Fact    : 0
% 7.40/2.56  #Define  : 0
% 7.40/2.56  #Split   : 16
% 7.40/2.56  #Chain   : 0
% 7.40/2.56  #Close   : 0
% 7.40/2.56  
% 7.40/2.56  Ordering : KBO
% 7.40/2.56  
% 7.40/2.56  Simplification rules
% 7.40/2.56  ----------------------
% 7.40/2.56  #Subsume      : 232
% 7.40/2.56  #Demod        : 411
% 7.40/2.56  #Tautology    : 138
% 7.40/2.56  #SimpNegUnit  : 17
% 7.40/2.56  #BackRed      : 16
% 7.40/2.56  
% 7.40/2.56  #Partial instantiations: 0
% 7.40/2.56  #Strategies tried      : 1
% 7.40/2.56  
% 7.40/2.56  Timing (in seconds)
% 7.40/2.56  ----------------------
% 7.40/2.57  Preprocessing        : 0.35
% 7.40/2.57  Parsing              : 0.18
% 7.40/2.57  CNF conversion       : 0.03
% 7.40/2.57  Main loop            : 1.44
% 7.40/2.57  Inferencing          : 0.47
% 7.40/2.57  Reduction            : 0.40
% 7.40/2.57  Demodulation         : 0.26
% 7.40/2.57  BG Simplification    : 0.05
% 7.40/2.57  Subsumption          : 0.42
% 7.40/2.57  Abstraction          : 0.06
% 7.40/2.57  MUC search           : 0.00
% 7.40/2.57  Cooper               : 0.00
% 7.40/2.57  Total                : 1.84
% 7.40/2.57  Index Insertion      : 0.00
% 7.40/2.57  Index Deletion       : 0.00
% 7.40/2.57  Index Matching       : 0.00
% 7.40/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
