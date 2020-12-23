%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1121+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:26 EST 2020

% Result     : Theorem 30.24s
% Output     : CNFRefutation 30.24s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 831 expanded)
%              Number of leaves         :   28 ( 290 expanded)
%              Depth                    :   23
%              Number of atoms          :  431 (2646 expanded)
%              Number of equality atoms :   16 ( 291 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v4_pre_topc(B,A)
               => k2_pre_topc(A,B) = B )
              & ( ( v2_pre_topc(A)
                  & k2_pre_topc(A,B) = B )
               => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ? [C] :
              ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
              & ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(D,C)
                  <=> ( v4_pre_topc(D,A)
                      & r1_tarski(B,D) ) ) )
              & k2_pre_topc(A,B) = k6_setfam_1(u1_struct_0(A),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( r2_hidden(C,B)
                 => v4_pre_topc(C,A) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_pre_topc)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( r2_hidden(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( ( v4_pre_topc(D,A)
                        & r1_tarski(B,D) )
                     => r2_hidden(C,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_62,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_65,plain,(
    v2_pre_topc('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_50,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    ! [A_40,B_48] :
      ( m1_subset_1('#skF_4'(A_40,B_48),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_40))))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_67,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( k2_pre_topc('#skF_5','#skF_6') != '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_78,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_52])).

tff(c_323,plain,(
    ! [A_107,B_108] :
      ( k6_setfam_1(u1_struct_0(A_107),'#skF_4'(A_107,B_108)) = k2_pre_topc(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_330,plain,
    ( k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_323])).

tff(c_335,plain,(
    k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_67,c_330])).

tff(c_24,plain,(
    ! [A_12,B_16] :
      ( m1_subset_1('#skF_2'(A_12,B_16),k1_zfmisc_1(u1_struct_0(A_12)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_12),B_16),A_12)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12)
      | ~ v2_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_179,plain,(
    ! [A_89,B_90] :
      ( m1_subset_1('#skF_4'(A_89,B_90),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_89))))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [A_89,B_90] :
      ( r1_tarski('#skF_4'(A_89,B_90),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89)
      | ~ v2_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_179,c_16])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_790,plain,(
    ! [A_148,B_149] :
      ( ~ v4_pre_topc('#skF_2'(A_148,B_149),A_148)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_148),B_149),A_148)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_148))))
      | ~ l1_pre_topc(A_148)
      | ~ v2_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1629,plain,(
    ! [A_199,A_200] :
      ( ~ v4_pre_topc('#skF_2'(A_199,A_200),A_199)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_199),A_200),A_199)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | ~ r1_tarski(A_200,k1_zfmisc_1(u1_struct_0(A_199))) ) ),
    inference(resolution,[status(thm)],[c_18,c_790])).

tff(c_1638,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_1629])).

tff(c_1642,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_1638])).

tff(c_1643,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1642])).

tff(c_1644,plain,(
    ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_1643])).

tff(c_1647,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_183,c_1644])).

tff(c_1651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_48,c_1647])).

tff(c_1652,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1643])).

tff(c_1653,plain,(
    r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_1643])).

tff(c_524,plain,(
    ! [A_125,B_126] :
      ( r2_hidden('#skF_2'(A_125,B_126),B_126)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_125),B_126),A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_125))))
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1952,plain,(
    ! [A_220,A_221] :
      ( r2_hidden('#skF_2'(A_220,A_221),A_221)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_220),A_221),A_220)
      | ~ l1_pre_topc(A_220)
      | ~ v2_pre_topc(A_220)
      | ~ r1_tarski(A_221,k1_zfmisc_1(u1_struct_0(A_220))) ) ),
    inference(resolution,[status(thm)],[c_18,c_524])).

tff(c_1969,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ r1_tarski('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_1952])).

tff(c_1974,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1653,c_65,c_50,c_1969])).

tff(c_1975,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1974])).

tff(c_44,plain,(
    ! [D_53,A_40,B_48] :
      ( v4_pre_topc(D_53,A_40)
      | ~ r2_hidden(D_53,'#skF_4'(A_40,B_48))
      | ~ m1_subset_1(D_53,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_40)))
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1979,plain,
    ( v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1975,c_44])).

tff(c_1987,plain,
    ( v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_48,c_1979])).

tff(c_1988,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1652,c_1987])).

tff(c_2016,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1988])).

tff(c_2022,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_335,c_2016])).

tff(c_2023,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_2022])).

tff(c_2027,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_2023])).

tff(c_2034,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50,c_48,c_2027])).

tff(c_2035,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_2038,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_52])).

tff(c_2081,plain,(
    ! [B_241,A_242] :
      ( r1_tarski(B_241,k2_pre_topc(A_242,B_241))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2086,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_2081])).

tff(c_2090,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2086])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2092,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2090,c_2])).

tff(c_2095,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_2038,c_2092])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k2_pre_topc(A_8,B_9),k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2100,plain,(
    ! [A_245,B_246] :
      ( m1_subset_1(k2_pre_topc(A_245,B_246),k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2107,plain,(
    ! [A_245,B_246] :
      ( r1_tarski(k2_pre_topc(A_245,B_246),u1_struct_0(A_245))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(resolution,[status(thm)],[c_2100,c_16])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2068,plain,(
    ! [C_235,B_236,A_237] :
      ( r2_hidden(C_235,B_236)
      | ~ r2_hidden(C_235,A_237)
      | ~ r1_tarski(A_237,B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2072,plain,(
    ! [A_238,B_239,B_240] :
      ( r2_hidden('#skF_1'(A_238,B_239),B_240)
      | ~ r1_tarski(A_238,B_240)
      | r1_tarski(A_238,B_239) ) ),
    inference(resolution,[status(thm)],[c_12,c_2068])).

tff(c_8,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2112,plain,(
    ! [A_249,B_250,B_251,B_252] :
      ( r2_hidden('#skF_1'(A_249,B_250),B_251)
      | ~ r1_tarski(B_252,B_251)
      | ~ r1_tarski(A_249,B_252)
      | r1_tarski(A_249,B_250) ) ),
    inference(resolution,[status(thm)],[c_2072,c_8])).

tff(c_11369,plain,(
    ! [A_749,B_750,A_751,B_752] :
      ( r2_hidden('#skF_1'(A_749,B_750),u1_struct_0(A_751))
      | ~ r1_tarski(A_749,k2_pre_topc(A_751,B_752))
      | r1_tarski(A_749,B_750)
      | ~ m1_subset_1(B_752,k1_zfmisc_1(u1_struct_0(A_751)))
      | ~ l1_pre_topc(A_751) ) ),
    inference(resolution,[status(thm)],[c_2107,c_2112])).

tff(c_11431,plain,(
    ! [A_753,B_754,B_755] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_753,B_754),B_755),u1_struct_0(A_753))
      | r1_tarski(k2_pre_topc(A_753,B_754),B_755)
      | ~ m1_subset_1(B_754,k1_zfmisc_1(u1_struct_0(A_753)))
      | ~ l1_pre_topc(A_753) ) ),
    inference(resolution,[status(thm)],[c_6,c_11369])).

tff(c_15135,plain,(
    ! [A_940,B_941,B_942,B_943] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_940,B_941),B_942),B_943)
      | ~ r1_tarski(u1_struct_0(A_940),B_943)
      | r1_tarski(k2_pre_topc(A_940,B_941),B_942)
      | ~ m1_subset_1(B_941,k1_zfmisc_1(u1_struct_0(A_940)))
      | ~ l1_pre_topc(A_940) ) ),
    inference(resolution,[status(thm)],[c_11431,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15189,plain,(
    ! [A_944,B_945,B_946] :
      ( ~ r1_tarski(u1_struct_0(A_944),B_945)
      | r1_tarski(k2_pre_topc(A_944,B_946),B_945)
      | ~ m1_subset_1(B_946,k1_zfmisc_1(u1_struct_0(A_944)))
      | ~ l1_pre_topc(A_944) ) ),
    inference(resolution,[status(thm)],[c_15135,c_10])).

tff(c_15202,plain,(
    ! [B_945] :
      ( ~ r1_tarski(u1_struct_0('#skF_5'),B_945)
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_945)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_15189])).

tff(c_15254,plain,(
    ! [B_949] :
      ( ~ r1_tarski(u1_struct_0('#skF_5'),B_949)
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_949) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_15202])).

tff(c_2087,plain,(
    ! [A_10,A_242] :
      ( r1_tarski(A_10,k2_pre_topc(A_242,A_10))
      | ~ l1_pre_topc(A_242)
      | ~ r1_tarski(A_10,u1_struct_0(A_242)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2081])).

tff(c_2978,plain,(
    ! [A_331,B_332,A_333,A_334] :
      ( r2_hidden('#skF_1'(A_331,B_332),k2_pre_topc(A_333,A_334))
      | ~ r1_tarski(A_331,A_334)
      | r1_tarski(A_331,B_332)
      | ~ l1_pre_topc(A_333)
      | ~ r1_tarski(A_334,u1_struct_0(A_333)) ) ),
    inference(resolution,[status(thm)],[c_2087,c_2112])).

tff(c_2989,plain,(
    ! [A_331,A_334,A_333] :
      ( ~ r1_tarski(A_331,A_334)
      | r1_tarski(A_331,k2_pre_topc(A_333,A_334))
      | ~ l1_pre_topc(A_333)
      | ~ r1_tarski(A_334,u1_struct_0(A_333)) ) ),
    inference(resolution,[status(thm)],[c_2978,c_10])).

tff(c_16485,plain,(
    ! [A_974,A_975] :
      ( ~ r1_tarski(A_974,k2_pre_topc('#skF_5','#skF_6'))
      | r1_tarski(A_974,k2_pre_topc(A_975,k2_pre_topc('#skF_5','#skF_6')))
      | ~ l1_pre_topc(A_975)
      | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0(A_975)) ) ),
    inference(resolution,[status(thm)],[c_15254,c_2989])).

tff(c_16491,plain,(
    ! [A_974] :
      ( ~ r1_tarski(A_974,k2_pre_topc('#skF_5','#skF_6'))
      | r1_tarski(A_974,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_16485])).

tff(c_16498,plain,(
    ! [A_976] :
      ( ~ r1_tarski(A_976,k2_pre_topc('#skF_5','#skF_6'))
      | r1_tarski(A_976,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16491])).

tff(c_2123,plain,(
    ! [A_249,B_250,A_245,B_246] :
      ( r2_hidden('#skF_1'(A_249,B_250),u1_struct_0(A_245))
      | ~ r1_tarski(A_249,k2_pre_topc(A_245,B_246))
      | r1_tarski(A_249,B_250)
      | ~ m1_subset_1(B_246,k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ l1_pre_topc(A_245) ) ),
    inference(resolution,[status(thm)],[c_2107,c_2112])).

tff(c_16575,plain,(
    ! [A_976,B_250] :
      ( r2_hidden('#skF_1'(A_976,B_250),u1_struct_0('#skF_5'))
      | r1_tarski(A_976,B_250)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_976,k2_pre_topc('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_16498,c_2123])).

tff(c_16782,plain,(
    ! [A_976,B_250] :
      ( r2_hidden('#skF_1'(A_976,B_250),u1_struct_0('#skF_5'))
      | r1_tarski(A_976,B_250)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_976,k2_pre_topc('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16575])).

tff(c_21741,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_16782])).

tff(c_21745,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_21741])).

tff(c_21752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_21745])).

tff(c_21754,plain,(
    m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_16782])).

tff(c_46,plain,(
    ! [B_56,A_54] :
      ( r1_tarski(B_56,k2_pre_topc(A_54,B_56))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_21778,plain,
    ( r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_21754,c_46])).

tff(c_21810,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_21778])).

tff(c_22105,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_250),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_250)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21810,c_2123])).

tff(c_22180,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_250),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_250) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_21754,c_22105])).

tff(c_7163,plain,(
    ! [C_544,D_545,B_546,A_547] :
      ( r2_hidden(C_544,D_545)
      | ~ r1_tarski(B_546,D_545)
      | ~ v4_pre_topc(D_545,A_547)
      | ~ m1_subset_1(D_545,k1_zfmisc_1(u1_struct_0(A_547)))
      | ~ r2_hidden(C_544,k2_pre_topc(A_547,B_546))
      | ~ r2_hidden(C_544,u1_struct_0(A_547))
      | ~ m1_subset_1(B_546,k1_zfmisc_1(u1_struct_0(A_547)))
      | ~ l1_pre_topc(A_547) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7884,plain,(
    ! [C_580,B_581,A_582] :
      ( r2_hidden(C_580,B_581)
      | ~ v4_pre_topc(B_581,A_582)
      | ~ r2_hidden(C_580,k2_pre_topc(A_582,B_581))
      | ~ r2_hidden(C_580,u1_struct_0(A_582))
      | ~ m1_subset_1(B_581,k1_zfmisc_1(u1_struct_0(A_582)))
      | ~ l1_pre_topc(A_582) ) ),
    inference(resolution,[status(thm)],[c_6,c_7163])).

tff(c_23554,plain,(
    ! [A_1146,B_1147,B_1148] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_1146,B_1147),B_1148),B_1147)
      | ~ v4_pre_topc(B_1147,A_1146)
      | ~ r2_hidden('#skF_1'(k2_pre_topc(A_1146,B_1147),B_1148),u1_struct_0(A_1146))
      | ~ m1_subset_1(B_1147,k1_zfmisc_1(u1_struct_0(A_1146)))
      | ~ l1_pre_topc(A_1146)
      | r1_tarski(k2_pre_topc(A_1146,B_1147),B_1148) ) ),
    inference(resolution,[status(thm)],[c_12,c_7884])).

tff(c_23562,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_250),'#skF_6')
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_250) ) ),
    inference(resolution,[status(thm)],[c_22180,c_23554])).

tff(c_23617,plain,(
    ! [B_1149] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1149),'#skF_6')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_2035,c_23562])).

tff(c_23623,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_23617,c_10])).

tff(c_23628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2095,c_2095,c_23623])).

tff(c_23630,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_60,plain,
    ( k2_pre_topc('#skF_5','#skF_6') != '#skF_6'
    | v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_23631,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_23630,c_60])).

tff(c_23678,plain,(
    ! [B_1166,A_1167] :
      ( r1_tarski(B_1166,k2_pre_topc(A_1167,B_1166))
      | ~ m1_subset_1(B_1166,k1_zfmisc_1(u1_struct_0(A_1167)))
      | ~ l1_pre_topc(A_1167) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_23683,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_23678])).

tff(c_23687,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_23683])).

tff(c_23689,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_23687,c_2])).

tff(c_23692,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_23631,c_23689])).

tff(c_23629,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_23693,plain,(
    ! [A_1168,B_1169] :
      ( m1_subset_1(k2_pre_topc(A_1168,B_1169),k1_zfmisc_1(u1_struct_0(A_1168)))
      | ~ m1_subset_1(B_1169,k1_zfmisc_1(u1_struct_0(A_1168)))
      | ~ l1_pre_topc(A_1168) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23700,plain,(
    ! [A_1168,B_1169] :
      ( r1_tarski(k2_pre_topc(A_1168,B_1169),u1_struct_0(A_1168))
      | ~ m1_subset_1(B_1169,k1_zfmisc_1(u1_struct_0(A_1168)))
      | ~ l1_pre_topc(A_1168) ) ),
    inference(resolution,[status(thm)],[c_23693,c_16])).

tff(c_23665,plain,(
    ! [C_1160,B_1161,A_1162] :
      ( r2_hidden(C_1160,B_1161)
      | ~ r2_hidden(C_1160,A_1162)
      | ~ r1_tarski(A_1162,B_1161) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_23669,plain,(
    ! [A_1163,B_1164,B_1165] :
      ( r2_hidden('#skF_1'(A_1163,B_1164),B_1165)
      | ~ r1_tarski(A_1163,B_1165)
      | r1_tarski(A_1163,B_1164) ) ),
    inference(resolution,[status(thm)],[c_12,c_23665])).

tff(c_23714,plain,(
    ! [A_1176,B_1177,B_1178,B_1179] :
      ( r2_hidden('#skF_1'(A_1176,B_1177),B_1178)
      | ~ r1_tarski(B_1179,B_1178)
      | ~ r1_tarski(A_1176,B_1179)
      | r1_tarski(A_1176,B_1177) ) ),
    inference(resolution,[status(thm)],[c_23669,c_8])).

tff(c_29075,plain,(
    ! [A_1540,B_1541,A_1542,B_1543] :
      ( r2_hidden('#skF_1'(A_1540,B_1541),u1_struct_0(A_1542))
      | ~ r1_tarski(A_1540,k2_pre_topc(A_1542,B_1543))
      | r1_tarski(A_1540,B_1541)
      | ~ m1_subset_1(B_1543,k1_zfmisc_1(u1_struct_0(A_1542)))
      | ~ l1_pre_topc(A_1542) ) ),
    inference(resolution,[status(thm)],[c_23700,c_23714])).

tff(c_29126,plain,(
    ! [A_1544,B_1545,B_1546] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_1544,B_1545),B_1546),u1_struct_0(A_1544))
      | r1_tarski(k2_pre_topc(A_1544,B_1545),B_1546)
      | ~ m1_subset_1(B_1545,k1_zfmisc_1(u1_struct_0(A_1544)))
      | ~ l1_pre_topc(A_1544) ) ),
    inference(resolution,[status(thm)],[c_6,c_29075])).

tff(c_30290,plain,(
    ! [A_1636,B_1637,B_1638,B_1639] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_1636,B_1637),B_1638),B_1639)
      | ~ r1_tarski(u1_struct_0(A_1636),B_1639)
      | r1_tarski(k2_pre_topc(A_1636,B_1637),B_1638)
      | ~ m1_subset_1(B_1637,k1_zfmisc_1(u1_struct_0(A_1636)))
      | ~ l1_pre_topc(A_1636) ) ),
    inference(resolution,[status(thm)],[c_29126,c_8])).

tff(c_30337,plain,(
    ! [A_1640,B_1641,B_1642] :
      ( ~ r1_tarski(u1_struct_0(A_1640),B_1641)
      | r1_tarski(k2_pre_topc(A_1640,B_1642),B_1641)
      | ~ m1_subset_1(B_1642,k1_zfmisc_1(u1_struct_0(A_1640)))
      | ~ l1_pre_topc(A_1640) ) ),
    inference(resolution,[status(thm)],[c_30290,c_10])).

tff(c_30350,plain,(
    ! [B_1641] :
      ( ~ r1_tarski(u1_struct_0('#skF_5'),B_1641)
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1641)
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_30337])).

tff(c_30361,plain,(
    ! [B_1643] :
      ( ~ r1_tarski(u1_struct_0('#skF_5'),B_1643)
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1643) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30350])).

tff(c_23684,plain,(
    ! [A_10,A_1167] :
      ( r1_tarski(A_10,k2_pre_topc(A_1167,A_10))
      | ~ l1_pre_topc(A_1167)
      | ~ r1_tarski(A_10,u1_struct_0(A_1167)) ) ),
    inference(resolution,[status(thm)],[c_18,c_23678])).

tff(c_24542,plain,(
    ! [A_1255,B_1256,A_1257,A_1258] :
      ( r2_hidden('#skF_1'(A_1255,B_1256),k2_pre_topc(A_1257,A_1258))
      | ~ r1_tarski(A_1255,A_1258)
      | r1_tarski(A_1255,B_1256)
      | ~ l1_pre_topc(A_1257)
      | ~ r1_tarski(A_1258,u1_struct_0(A_1257)) ) ),
    inference(resolution,[status(thm)],[c_23684,c_23714])).

tff(c_24553,plain,(
    ! [A_1255,A_1258,A_1257] :
      ( ~ r1_tarski(A_1255,A_1258)
      | r1_tarski(A_1255,k2_pre_topc(A_1257,A_1258))
      | ~ l1_pre_topc(A_1257)
      | ~ r1_tarski(A_1258,u1_struct_0(A_1257)) ) ),
    inference(resolution,[status(thm)],[c_24542,c_10])).

tff(c_31440,plain,(
    ! [A_1674,A_1675] :
      ( ~ r1_tarski(A_1674,k2_pre_topc('#skF_5','#skF_6'))
      | r1_tarski(A_1674,k2_pre_topc(A_1675,k2_pre_topc('#skF_5','#skF_6')))
      | ~ l1_pre_topc(A_1675)
      | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0(A_1675)) ) ),
    inference(resolution,[status(thm)],[c_30361,c_24553])).

tff(c_31446,plain,(
    ! [A_1674] :
      ( ~ r1_tarski(A_1674,k2_pre_topc('#skF_5','#skF_6'))
      | r1_tarski(A_1674,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6,c_31440])).

tff(c_31453,plain,(
    ! [A_1676] :
      ( ~ r1_tarski(A_1676,k2_pre_topc('#skF_5','#skF_6'))
      | r1_tarski(A_1676,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_31446])).

tff(c_23725,plain,(
    ! [A_1176,B_1177,A_1168,B_1169] :
      ( r2_hidden('#skF_1'(A_1176,B_1177),u1_struct_0(A_1168))
      | ~ r1_tarski(A_1176,k2_pre_topc(A_1168,B_1169))
      | r1_tarski(A_1176,B_1177)
      | ~ m1_subset_1(B_1169,k1_zfmisc_1(u1_struct_0(A_1168)))
      | ~ l1_pre_topc(A_1168) ) ),
    inference(resolution,[status(thm)],[c_23700,c_23714])).

tff(c_31494,plain,(
    ! [A_1676,B_1177] :
      ( r2_hidden('#skF_1'(A_1676,B_1177),u1_struct_0('#skF_5'))
      | r1_tarski(A_1676,B_1177)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ r1_tarski(A_1676,k2_pre_topc('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_31453,c_23725])).

tff(c_31613,plain,(
    ! [A_1676,B_1177] :
      ( r2_hidden('#skF_1'(A_1676,B_1177),u1_struct_0('#skF_5'))
      | r1_tarski(A_1676,B_1177)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_tarski(A_1676,k2_pre_topc('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_31494])).

tff(c_33293,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_31613])).

tff(c_33296,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_33293])).

tff(c_33303,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_33296])).

tff(c_33305,plain,(
    m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_31613])).

tff(c_33321,plain,
    ( r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_33305,c_46])).

tff(c_33348,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_33321])).

tff(c_33568,plain,(
    ! [B_1177] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1177),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1177)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_33348,c_23725])).

tff(c_33628,plain,(
    ! [B_1177] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1177),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_33305,c_33568])).

tff(c_27960,plain,(
    ! [C_1477,D_1478,B_1479,A_1480] :
      ( r2_hidden(C_1477,D_1478)
      | ~ r1_tarski(B_1479,D_1478)
      | ~ v4_pre_topc(D_1478,A_1480)
      | ~ m1_subset_1(D_1478,k1_zfmisc_1(u1_struct_0(A_1480)))
      | ~ r2_hidden(C_1477,k2_pre_topc(A_1480,B_1479))
      | ~ r2_hidden(C_1477,u1_struct_0(A_1480))
      | ~ m1_subset_1(B_1479,k1_zfmisc_1(u1_struct_0(A_1480)))
      | ~ l1_pre_topc(A_1480) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28747,plain,(
    ! [C_1524,B_1525,A_1526] :
      ( r2_hidden(C_1524,B_1525)
      | ~ v4_pre_topc(B_1525,A_1526)
      | ~ r2_hidden(C_1524,k2_pre_topc(A_1526,B_1525))
      | ~ r2_hidden(C_1524,u1_struct_0(A_1526))
      | ~ m1_subset_1(B_1525,k1_zfmisc_1(u1_struct_0(A_1526)))
      | ~ l1_pre_topc(A_1526) ) ),
    inference(resolution,[status(thm)],[c_6,c_27960])).

tff(c_70923,plain,(
    ! [A_14172,B_14173,B_14174] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_14172,B_14173),B_14174),B_14173)
      | ~ v4_pre_topc(B_14173,A_14172)
      | ~ r2_hidden('#skF_1'(k2_pre_topc(A_14172,B_14173),B_14174),u1_struct_0(A_14172))
      | ~ m1_subset_1(B_14173,k1_zfmisc_1(u1_struct_0(A_14172)))
      | ~ l1_pre_topc(A_14172)
      | r1_tarski(k2_pre_topc(A_14172,B_14173),B_14174) ) ),
    inference(resolution,[status(thm)],[c_12,c_28747])).

tff(c_71006,plain,(
    ! [B_1177] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1177),'#skF_6')
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1177) ) ),
    inference(resolution,[status(thm)],[c_33628,c_70923])).

tff(c_71062,plain,(
    ! [B_14205] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_14205),'#skF_6')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_14205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_23629,c_71006])).

tff(c_71068,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_71062,c_10])).

tff(c_71119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23692,c_23692,c_71068])).

%------------------------------------------------------------------------------
