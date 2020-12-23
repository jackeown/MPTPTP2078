%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:10 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.69s
% Verified   : 
% Statistics : Number of formulae       :  233 (1291 expanded)
%              Number of leaves         :   51 ( 474 expanded)
%              Depth                    :   20
%              Number of atoms          :  705 (5662 expanded)
%              Number of equality atoms :   44 ( 294 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v6_waybel_0 > v4_yellow_0 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(v4_yellow_0,type,(
    v4_yellow_0: ( $i * $i ) > $o )).

tff(k1_toler_1,type,(
    k1_toler_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(m1_yellow_0,type,(
    m1_yellow_0: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff(m1_yellow_6,type,(
    m1_yellow_6: ( $i * $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_yellow_6,type,(
    v2_yellow_6: ( $i * $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => ( v2_yellow_6(k4_waybel_9(A,B,C),A,B)
                  & m1_yellow_6(k4_waybel_9(A,B,C),A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_waybel_9)).

tff(f_162,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_146,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k4_waybel_9(A,B,C)
                  <=> ( ! [E] :
                          ( r2_hidden(E,u1_struct_0(D))
                        <=> ? [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                              & F = E
                              & r1_orders_2(B,C,F) ) )
                      & r2_relset_1(u1_struct_0(D),u1_struct_0(D),u1_orders_2(D),k1_toler_1(u1_orders_2(B),u1_struct_0(D)))
                      & u1_waybel_0(A,D) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( l1_waybel_0(C,A)
             => ( m1_yellow_6(C,A,B)
              <=> ( m1_yellow_0(C,B)
                  & u1_waybel_0(A,C) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_yellow_6)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ! [C] :
              ( m1_yellow_6(C,A,B)
             => ( v2_yellow_6(C,A,B)
              <=> ( v4_yellow_0(C,B)
                  & m1_yellow_0(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_6)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(u1_orders_2(A),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => m1_subset_1(k1_toler_1(A,B),k1_zfmisc_1(k2_zfmisc_1(B,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_toler_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => k1_toler_1(A,B) = k2_wellord1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_toler_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_orders_2(B)
         => ( m1_yellow_0(B,A)
          <=> ( r1_tarski(u1_struct_0(B),u1_struct_0(A))
              & r1_tarski(u1_orders_2(B),u1_orders_2(A)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_yellow_0)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_yellow_0(B,A)
         => ( v4_yellow_0(B,A)
          <=> u1_orders_2(B) = k1_toler_1(u1_orders_2(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_yellow_0)).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_84,plain,(
    l1_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_80,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_4894,plain,(
    ! [A_1723,B_1724,C_1725] :
      ( l1_waybel_0(k4_waybel_9(A_1723,B_1724,C_1725),A_1723)
      | ~ m1_subset_1(C_1725,u1_struct_0(B_1724))
      | ~ l1_waybel_0(B_1724,A_1723)
      | v2_struct_0(B_1724)
      | ~ l1_struct_0(A_1723)
      | v2_struct_0(A_1723) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4896,plain,(
    ! [A_1723] :
      ( l1_waybel_0(k4_waybel_9(A_1723,'#skF_6','#skF_7'),A_1723)
      | ~ l1_waybel_0('#skF_6',A_1723)
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0(A_1723)
      | v2_struct_0(A_1723) ) ),
    inference(resolution,[status(thm)],[c_78,c_4894])).

tff(c_4899,plain,(
    ! [A_1723] :
      ( l1_waybel_0(k4_waybel_9(A_1723,'#skF_6','#skF_7'),A_1723)
      | ~ l1_waybel_0('#skF_6',A_1723)
      | ~ l1_struct_0(A_1723)
      | v2_struct_0(A_1723) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4896])).

tff(c_72,plain,(
    ! [A_213,B_214,C_215] :
      ( v6_waybel_0(k4_waybel_9(A_213,B_214,C_215),A_213)
      | ~ m1_subset_1(C_215,u1_struct_0(B_214))
      | ~ l1_waybel_0(B_214,A_213)
      | v2_struct_0(B_214)
      | ~ l1_struct_0(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_5137,plain,(
    ! [B_1830,A_1831,C_1832] :
      ( k2_partfun1(u1_struct_0(B_1830),u1_struct_0(A_1831),u1_waybel_0(A_1831,B_1830),u1_struct_0(k4_waybel_9(A_1831,B_1830,C_1832))) = u1_waybel_0(A_1831,k4_waybel_9(A_1831,B_1830,C_1832))
      | ~ l1_waybel_0(k4_waybel_9(A_1831,B_1830,C_1832),A_1831)
      | ~ v6_waybel_0(k4_waybel_9(A_1831,B_1830,C_1832),A_1831)
      | ~ m1_subset_1(C_1832,u1_struct_0(B_1830))
      | ~ l1_waybel_0(B_1830,A_1831)
      | v2_struct_0(B_1830)
      | ~ l1_struct_0(A_1831)
      | v2_struct_0(A_1831) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30,plain,(
    ! [C_33,A_27,B_31] :
      ( m1_yellow_6(C_33,A_27,B_31)
      | k2_partfun1(u1_struct_0(B_31),u1_struct_0(A_27),u1_waybel_0(A_27,B_31),u1_struct_0(C_33)) != u1_waybel_0(A_27,C_33)
      | ~ m1_yellow_0(C_33,B_31)
      | ~ l1_waybel_0(C_33,A_27)
      | ~ l1_waybel_0(B_31,A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5346,plain,(
    ! [A_1914,B_1915,C_1916] :
      ( m1_yellow_6(k4_waybel_9(A_1914,B_1915,C_1916),A_1914,B_1915)
      | ~ m1_yellow_0(k4_waybel_9(A_1914,B_1915,C_1916),B_1915)
      | ~ l1_waybel_0(k4_waybel_9(A_1914,B_1915,C_1916),A_1914)
      | ~ v6_waybel_0(k4_waybel_9(A_1914,B_1915,C_1916),A_1914)
      | ~ m1_subset_1(C_1916,u1_struct_0(B_1915))
      | ~ l1_waybel_0(B_1915,A_1914)
      | v2_struct_0(B_1915)
      | ~ l1_struct_0(A_1914)
      | v2_struct_0(A_1914) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5137,c_30])).

tff(c_2453,plain,(
    ! [A_982,B_983,C_984] :
      ( l1_waybel_0(k4_waybel_9(A_982,B_983,C_984),A_982)
      | ~ m1_subset_1(C_984,u1_struct_0(B_983))
      | ~ l1_waybel_0(B_983,A_982)
      | v2_struct_0(B_983)
      | ~ l1_struct_0(A_982)
      | v2_struct_0(A_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2455,plain,(
    ! [A_982] :
      ( l1_waybel_0(k4_waybel_9(A_982,'#skF_6','#skF_7'),A_982)
      | ~ l1_waybel_0('#skF_6',A_982)
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0(A_982)
      | v2_struct_0(A_982) ) ),
    inference(resolution,[status(thm)],[c_78,c_2453])).

tff(c_2460,plain,(
    ! [A_985] :
      ( l1_waybel_0(k4_waybel_9(A_985,'#skF_6','#skF_7'),A_985)
      | ~ l1_waybel_0('#skF_6',A_985)
      | ~ l1_struct_0(A_985)
      | v2_struct_0(A_985) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2455])).

tff(c_28,plain,(
    ! [B_26,A_24] :
      ( l1_orders_2(B_26)
      | ~ l1_waybel_0(B_26,A_24)
      | ~ l1_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2464,plain,(
    ! [A_985] :
      ( l1_orders_2(k4_waybel_9(A_985,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_985)
      | ~ l1_struct_0(A_985)
      | v2_struct_0(A_985) ) ),
    inference(resolution,[status(thm)],[c_2460,c_28])).

tff(c_2433,plain,(
    ! [A_978,B_979,C_980] :
      ( l1_waybel_0(k4_waybel_9(A_978,B_979,C_980),A_978)
      | ~ m1_subset_1(C_980,u1_struct_0(B_979))
      | ~ l1_waybel_0(B_979,A_978)
      | v2_struct_0(B_979)
      | ~ l1_struct_0(A_978)
      | v2_struct_0(A_978) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_2435,plain,(
    ! [A_978] :
      ( l1_waybel_0(k4_waybel_9(A_978,'#skF_6','#skF_7'),A_978)
      | ~ l1_waybel_0('#skF_6',A_978)
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0(A_978)
      | v2_struct_0(A_978) ) ),
    inference(resolution,[status(thm)],[c_78,c_2433])).

tff(c_2439,plain,(
    ! [A_981] :
      ( l1_waybel_0(k4_waybel_9(A_981,'#skF_6','#skF_7'),A_981)
      | ~ l1_waybel_0('#skF_6',A_981)
      | ~ l1_struct_0(A_981)
      | v2_struct_0(A_981) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2435])).

tff(c_244,plain,(
    ! [A_297,B_298,C_299] :
      ( l1_waybel_0(k4_waybel_9(A_297,B_298,C_299),A_297)
      | ~ m1_subset_1(C_299,u1_struct_0(B_298))
      | ~ l1_waybel_0(B_298,A_297)
      | v2_struct_0(B_298)
      | ~ l1_struct_0(A_297)
      | v2_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_246,plain,(
    ! [A_297] :
      ( l1_waybel_0(k4_waybel_9(A_297,'#skF_6','#skF_7'),A_297)
      | ~ l1_waybel_0('#skF_6',A_297)
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0(A_297)
      | v2_struct_0(A_297) ) ),
    inference(resolution,[status(thm)],[c_78,c_244])).

tff(c_249,plain,(
    ! [A_297] :
      ( l1_waybel_0(k4_waybel_9(A_297,'#skF_6','#skF_7'),A_297)
      | ~ l1_waybel_0('#skF_6',A_297)
      | ~ l1_struct_0(A_297)
      | v2_struct_0(A_297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_246])).

tff(c_408,plain,(
    ! [B_367,A_368,C_369] :
      ( k2_partfun1(u1_struct_0(B_367),u1_struct_0(A_368),u1_waybel_0(A_368,B_367),u1_struct_0(k4_waybel_9(A_368,B_367,C_369))) = u1_waybel_0(A_368,k4_waybel_9(A_368,B_367,C_369))
      | ~ l1_waybel_0(k4_waybel_9(A_368,B_367,C_369),A_368)
      | ~ v6_waybel_0(k4_waybel_9(A_368,B_367,C_369),A_368)
      | ~ m1_subset_1(C_369,u1_struct_0(B_367))
      | ~ l1_waybel_0(B_367,A_368)
      | v2_struct_0(B_367)
      | ~ l1_struct_0(A_368)
      | v2_struct_0(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_686,plain,(
    ! [A_481,B_482,C_483] :
      ( m1_yellow_6(k4_waybel_9(A_481,B_482,C_483),A_481,B_482)
      | ~ m1_yellow_0(k4_waybel_9(A_481,B_482,C_483),B_482)
      | ~ l1_waybel_0(k4_waybel_9(A_481,B_482,C_483),A_481)
      | ~ v6_waybel_0(k4_waybel_9(A_481,B_482,C_483),A_481)
      | ~ m1_subset_1(C_483,u1_struct_0(B_482))
      | ~ l1_waybel_0(B_482,A_481)
      | v2_struct_0(B_482)
      | ~ l1_struct_0(A_481)
      | v2_struct_0(A_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_30])).

tff(c_227,plain,(
    ! [C_291,A_292,B_293] :
      ( v2_yellow_6(C_291,A_292,B_293)
      | ~ m1_yellow_0(C_291,B_293)
      | ~ v4_yellow_0(C_291,B_293)
      | ~ m1_yellow_6(C_291,A_292,B_293)
      | ~ l1_waybel_0(B_293,A_292)
      | ~ l1_struct_0(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_76,plain,
    ( ~ m1_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6')
    | ~ v2_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_96,plain,(
    ~ v2_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_236,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ v4_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_227,c_96])).

tff(c_241,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ v4_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_236])).

tff(c_243,plain,(
    ~ m1_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_241])).

tff(c_689,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_686,c_243])).

tff(c_695,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_689])).

tff(c_696,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_695])).

tff(c_698,plain,(
    ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_696])).

tff(c_701,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_698])).

tff(c_704,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_701])).

tff(c_706,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_704])).

tff(c_707,plain,
    ( ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_716,plain,(
    ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_707])).

tff(c_88,plain,(
    ! [B_229,A_230] :
      ( l1_orders_2(B_229)
      | ~ l1_waybel_0(B_229,A_230)
      | ~ l1_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_91,plain,
    ( l1_orders_2('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_88])).

tff(c_94,plain,(
    l1_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_91])).

tff(c_250,plain,(
    ! [A_300] :
      ( l1_waybel_0(k4_waybel_9(A_300,'#skF_6','#skF_7'),A_300)
      | ~ l1_waybel_0('#skF_6',A_300)
      | ~ l1_struct_0(A_300)
      | v2_struct_0(A_300) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_246])).

tff(c_254,plain,(
    ! [A_300] :
      ( l1_orders_2(k4_waybel_9(A_300,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_300)
      | ~ l1_struct_0(A_300)
      | v2_struct_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_250,c_28])).

tff(c_708,plain,(
    v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_696])).

tff(c_12,plain,(
    ! [A_13] :
      ( m1_subset_1(u1_orders_2(A_13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13),u1_struct_0(A_13))))
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k1_toler_1(A_20,B_21),k1_zfmisc_1(k2_zfmisc_1(B_21,B_21)))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_540,plain,(
    ! [A_412,B_413,C_414] :
      ( r2_relset_1(u1_struct_0(k4_waybel_9(A_412,B_413,C_414)),u1_struct_0(k4_waybel_9(A_412,B_413,C_414)),u1_orders_2(k4_waybel_9(A_412,B_413,C_414)),k1_toler_1(u1_orders_2(B_413),u1_struct_0(k4_waybel_9(A_412,B_413,C_414))))
      | ~ l1_waybel_0(k4_waybel_9(A_412,B_413,C_414),A_412)
      | ~ v6_waybel_0(k4_waybel_9(A_412,B_413,C_414),A_412)
      | ~ m1_subset_1(C_414,u1_struct_0(B_413))
      | ~ l1_waybel_0(B_413,A_412)
      | v2_struct_0(B_413)
      | ~ l1_struct_0(A_412)
      | v2_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10,plain,(
    ! [D_12,C_11,A_9,B_10] :
      ( D_12 = C_11
      | ~ r2_relset_1(A_9,B_10,C_11,D_12)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1281,plain,(
    ! [B_746,A_747,C_748] :
      ( k1_toler_1(u1_orders_2(B_746),u1_struct_0(k4_waybel_9(A_747,B_746,C_748))) = u1_orders_2(k4_waybel_9(A_747,B_746,C_748))
      | ~ m1_subset_1(k1_toler_1(u1_orders_2(B_746),u1_struct_0(k4_waybel_9(A_747,B_746,C_748))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_747,B_746,C_748)),u1_struct_0(k4_waybel_9(A_747,B_746,C_748)))))
      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(A_747,B_746,C_748)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_747,B_746,C_748)),u1_struct_0(k4_waybel_9(A_747,B_746,C_748)))))
      | ~ l1_waybel_0(k4_waybel_9(A_747,B_746,C_748),A_747)
      | ~ v6_waybel_0(k4_waybel_9(A_747,B_746,C_748),A_747)
      | ~ m1_subset_1(C_748,u1_struct_0(B_746))
      | ~ l1_waybel_0(B_746,A_747)
      | v2_struct_0(B_746)
      | ~ l1_struct_0(A_747)
      | v2_struct_0(A_747) ) ),
    inference(resolution,[status(thm)],[c_540,c_10])).

tff(c_1757,plain,(
    ! [B_903,A_904,C_905] :
      ( k1_toler_1(u1_orders_2(B_903),u1_struct_0(k4_waybel_9(A_904,B_903,C_905))) = u1_orders_2(k4_waybel_9(A_904,B_903,C_905))
      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(A_904,B_903,C_905)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_904,B_903,C_905)),u1_struct_0(k4_waybel_9(A_904,B_903,C_905)))))
      | ~ l1_waybel_0(k4_waybel_9(A_904,B_903,C_905),A_904)
      | ~ v6_waybel_0(k4_waybel_9(A_904,B_903,C_905),A_904)
      | ~ m1_subset_1(C_905,u1_struct_0(B_903))
      | ~ l1_waybel_0(B_903,A_904)
      | v2_struct_0(B_903)
      | ~ l1_struct_0(A_904)
      | v2_struct_0(A_904)
      | ~ v1_relat_1(u1_orders_2(B_903)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1281])).

tff(c_1920,plain,(
    ! [B_958,A_959,C_960] :
      ( k1_toler_1(u1_orders_2(B_958),u1_struct_0(k4_waybel_9(A_959,B_958,C_960))) = u1_orders_2(k4_waybel_9(A_959,B_958,C_960))
      | ~ l1_waybel_0(k4_waybel_9(A_959,B_958,C_960),A_959)
      | ~ v6_waybel_0(k4_waybel_9(A_959,B_958,C_960),A_959)
      | ~ m1_subset_1(C_960,u1_struct_0(B_958))
      | ~ l1_waybel_0(B_958,A_959)
      | v2_struct_0(B_958)
      | ~ l1_struct_0(A_959)
      | v2_struct_0(A_959)
      | ~ v1_relat_1(u1_orders_2(B_958))
      | ~ l1_orders_2(k4_waybel_9(A_959,B_958,C_960)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1757])).

tff(c_1922,plain,
    ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_708,c_1920])).

tff(c_1927,plain,
    ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_1922])).

tff(c_1928,plain,
    ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_1927])).

tff(c_1930,plain,(
    ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1928])).

tff(c_1937,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_254,c_1930])).

tff(c_1940,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_1937])).

tff(c_1942,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1940])).

tff(c_1944,plain,(
    l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1928])).

tff(c_124,plain,(
    ! [A_247] :
      ( m1_subset_1(u1_orders_2(A_247),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247),u1_struct_0(A_247))))
      | ~ l1_orders_2(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [C_8,A_6,B_7] :
      ( v1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_131,plain,(
    ! [A_247] :
      ( v1_relat_1(u1_orders_2(A_247))
      | ~ l1_orders_2(A_247) ) ),
    inference(resolution,[status(thm)],[c_124,c_6])).

tff(c_1943,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1928])).

tff(c_1945,plain,(
    ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1943])).

tff(c_1949,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_249,c_1945])).

tff(c_1952,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_1949])).

tff(c_1954,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1952])).

tff(c_1955,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_6'))
    | k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1943])).

tff(c_1991,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1955])).

tff(c_1994,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_131,c_1991])).

tff(c_1998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_1994])).

tff(c_2000,plain,(
    v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_1999,plain,(
    k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1955])).

tff(c_132,plain,(
    ! [A_248] :
      ( v1_relat_1(u1_orders_2(A_248))
      | ~ l1_orders_2(A_248) ) ),
    inference(resolution,[status(thm)],[c_124,c_6])).

tff(c_26,plain,(
    ! [A_22,B_23] :
      ( k2_wellord1(A_22,B_23) = k1_toler_1(A_22,B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_137,plain,(
    ! [A_251,B_252] :
      ( k2_wellord1(u1_orders_2(A_251),B_252) = k1_toler_1(u1_orders_2(A_251),B_252)
      | ~ l1_orders_2(A_251) ) ),
    inference(resolution,[status(thm)],[c_132,c_26])).

tff(c_98,plain,(
    ! [A_236,B_237] :
      ( k3_xboole_0(A_236,k2_zfmisc_1(B_237,B_237)) = k2_wellord1(A_236,B_237)
      | ~ v1_relat_1(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_236,B_237] :
      ( r1_tarski(k2_wellord1(A_236,B_237),A_236)
      | ~ v1_relat_1(A_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2])).

tff(c_143,plain,(
    ! [A_251,B_252] :
      ( r1_tarski(k1_toler_1(u1_orders_2(A_251),B_252),u1_orders_2(A_251))
      | ~ v1_relat_1(u1_orders_2(A_251))
      | ~ l1_orders_2(A_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_104])).

tff(c_2247,plain,
    ( r1_tarski(u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')),u1_orders_2('#skF_6'))
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1999,c_143])).

tff(c_2379,plain,(
    r1_tarski(u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2000,c_2247])).

tff(c_260,plain,(
    ! [A_304,B_305,C_306] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(A_304,B_305,C_306)),u1_struct_0(B_305))
      | ~ m1_subset_1(C_306,u1_struct_0(B_305))
      | ~ l1_waybel_0(B_305,A_304)
      | v2_struct_0(B_305)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_14,plain,(
    ! [B_16,A_14] :
      ( m1_yellow_0(B_16,A_14)
      | ~ r1_tarski(u1_orders_2(B_16),u1_orders_2(A_14))
      | ~ r1_tarski(u1_struct_0(B_16),u1_struct_0(A_14))
      | ~ l1_orders_2(B_16)
      | ~ l1_orders_2(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_264,plain,(
    ! [A_304,B_305,C_306] :
      ( m1_yellow_0(k4_waybel_9(A_304,B_305,C_306),B_305)
      | ~ r1_tarski(u1_orders_2(k4_waybel_9(A_304,B_305,C_306)),u1_orders_2(B_305))
      | ~ l1_orders_2(k4_waybel_9(A_304,B_305,C_306))
      | ~ l1_orders_2(B_305)
      | ~ m1_subset_1(C_306,u1_struct_0(B_305))
      | ~ l1_waybel_0(B_305,A_304)
      | v2_struct_0(B_305)
      | ~ l1_struct_0(A_304)
      | v2_struct_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_260,c_14])).

tff(c_2400,plain,
    ( m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2379,c_264])).

tff(c_2403,plain,
    ( m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_94,c_1944,c_2400])).

tff(c_2405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_716,c_2403])).

tff(c_2406,plain,(
    ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_707])).

tff(c_2417,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_249,c_2406])).

tff(c_2420,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_2417])).

tff(c_2422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2420])).

tff(c_2423,plain,
    ( ~ v4_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_2431,plain,(
    ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2423])).

tff(c_2424,plain,(
    m1_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_241])).

tff(c_34,plain,(
    ! [C_33,B_31,A_27] :
      ( m1_yellow_0(C_33,B_31)
      | ~ m1_yellow_6(C_33,A_27,B_31)
      | ~ l1_waybel_0(C_33,A_27)
      | ~ l1_waybel_0(B_31,A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2427,plain,
    ( m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2424,c_34])).

tff(c_2430,plain,
    ( m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_2427])).

tff(c_2432,plain,(
    ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_2431,c_2430])).

tff(c_2442,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2439,c_2432])).

tff(c_2448,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_2442])).

tff(c_2450,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_2448])).

tff(c_2452,plain,(
    m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2423])).

tff(c_2458,plain,(
    ! [A_982] :
      ( l1_waybel_0(k4_waybel_9(A_982,'#skF_6','#skF_7'),A_982)
      | ~ l1_waybel_0('#skF_6',A_982)
      | ~ l1_struct_0(A_982)
      | v2_struct_0(A_982) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_2455])).

tff(c_2739,plain,(
    ! [A_1094,B_1095,C_1096] :
      ( r2_relset_1(u1_struct_0(k4_waybel_9(A_1094,B_1095,C_1096)),u1_struct_0(k4_waybel_9(A_1094,B_1095,C_1096)),u1_orders_2(k4_waybel_9(A_1094,B_1095,C_1096)),k1_toler_1(u1_orders_2(B_1095),u1_struct_0(k4_waybel_9(A_1094,B_1095,C_1096))))
      | ~ l1_waybel_0(k4_waybel_9(A_1094,B_1095,C_1096),A_1094)
      | ~ v6_waybel_0(k4_waybel_9(A_1094,B_1095,C_1096),A_1094)
      | ~ m1_subset_1(C_1096,u1_struct_0(B_1095))
      | ~ l1_waybel_0(B_1095,A_1094)
      | v2_struct_0(B_1095)
      | ~ l1_struct_0(A_1094)
      | v2_struct_0(A_1094) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3479,plain,(
    ! [B_1441,A_1442,C_1443] :
      ( k1_toler_1(u1_orders_2(B_1441),u1_struct_0(k4_waybel_9(A_1442,B_1441,C_1443))) = u1_orders_2(k4_waybel_9(A_1442,B_1441,C_1443))
      | ~ m1_subset_1(k1_toler_1(u1_orders_2(B_1441),u1_struct_0(k4_waybel_9(A_1442,B_1441,C_1443))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_1442,B_1441,C_1443)),u1_struct_0(k4_waybel_9(A_1442,B_1441,C_1443)))))
      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(A_1442,B_1441,C_1443)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_1442,B_1441,C_1443)),u1_struct_0(k4_waybel_9(A_1442,B_1441,C_1443)))))
      | ~ l1_waybel_0(k4_waybel_9(A_1442,B_1441,C_1443),A_1442)
      | ~ v6_waybel_0(k4_waybel_9(A_1442,B_1441,C_1443),A_1442)
      | ~ m1_subset_1(C_1443,u1_struct_0(B_1441))
      | ~ l1_waybel_0(B_1441,A_1442)
      | v2_struct_0(B_1441)
      | ~ l1_struct_0(A_1442)
      | v2_struct_0(A_1442) ) ),
    inference(resolution,[status(thm)],[c_2739,c_10])).

tff(c_3947,plain,(
    ! [B_1590,A_1591,C_1592] :
      ( k1_toler_1(u1_orders_2(B_1590),u1_struct_0(k4_waybel_9(A_1591,B_1590,C_1592))) = u1_orders_2(k4_waybel_9(A_1591,B_1590,C_1592))
      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(A_1591,B_1590,C_1592)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_1591,B_1590,C_1592)),u1_struct_0(k4_waybel_9(A_1591,B_1590,C_1592)))))
      | ~ l1_waybel_0(k4_waybel_9(A_1591,B_1590,C_1592),A_1591)
      | ~ v6_waybel_0(k4_waybel_9(A_1591,B_1590,C_1592),A_1591)
      | ~ m1_subset_1(C_1592,u1_struct_0(B_1590))
      | ~ l1_waybel_0(B_1590,A_1591)
      | v2_struct_0(B_1590)
      | ~ l1_struct_0(A_1591)
      | v2_struct_0(A_1591)
      | ~ v1_relat_1(u1_orders_2(B_1590)) ) ),
    inference(resolution,[status(thm)],[c_24,c_3479])).

tff(c_4110,plain,(
    ! [B_1645,A_1646,C_1647] :
      ( k1_toler_1(u1_orders_2(B_1645),u1_struct_0(k4_waybel_9(A_1646,B_1645,C_1647))) = u1_orders_2(k4_waybel_9(A_1646,B_1645,C_1647))
      | ~ l1_waybel_0(k4_waybel_9(A_1646,B_1645,C_1647),A_1646)
      | ~ v6_waybel_0(k4_waybel_9(A_1646,B_1645,C_1647),A_1646)
      | ~ m1_subset_1(C_1647,u1_struct_0(B_1645))
      | ~ l1_waybel_0(B_1645,A_1646)
      | v2_struct_0(B_1645)
      | ~ l1_struct_0(A_1646)
      | v2_struct_0(A_1646)
      | ~ v1_relat_1(u1_orders_2(B_1645))
      | ~ l1_orders_2(k4_waybel_9(A_1646,B_1645,C_1647)) ) ),
    inference(resolution,[status(thm)],[c_12,c_3947])).

tff(c_4114,plain,(
    ! [B_1648,A_1649,C_1650] :
      ( k1_toler_1(u1_orders_2(B_1648),u1_struct_0(k4_waybel_9(A_1649,B_1648,C_1650))) = u1_orders_2(k4_waybel_9(A_1649,B_1648,C_1650))
      | ~ l1_waybel_0(k4_waybel_9(A_1649,B_1648,C_1650),A_1649)
      | ~ v1_relat_1(u1_orders_2(B_1648))
      | ~ l1_orders_2(k4_waybel_9(A_1649,B_1648,C_1650))
      | ~ m1_subset_1(C_1650,u1_struct_0(B_1648))
      | ~ l1_waybel_0(B_1648,A_1649)
      | v2_struct_0(B_1648)
      | ~ l1_struct_0(A_1649)
      | v2_struct_0(A_1649) ) ),
    inference(resolution,[status(thm)],[c_72,c_4110])).

tff(c_4120,plain,(
    ! [A_982] :
      ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9(A_982,'#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9(A_982,'#skF_6','#skF_7'))
      | ~ v1_relat_1(u1_orders_2('#skF_6'))
      | ~ l1_orders_2(k4_waybel_9(A_982,'#skF_6','#skF_7'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0('#skF_6',A_982)
      | ~ l1_struct_0(A_982)
      | v2_struct_0(A_982) ) ),
    inference(resolution,[status(thm)],[c_2458,c_4114])).

tff(c_4127,plain,(
    ! [A_982] :
      ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9(A_982,'#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9(A_982,'#skF_6','#skF_7'))
      | ~ v1_relat_1(u1_orders_2('#skF_6'))
      | ~ l1_orders_2(k4_waybel_9(A_982,'#skF_6','#skF_7'))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0('#skF_6',A_982)
      | ~ l1_struct_0(A_982)
      | v2_struct_0(A_982) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4120])).

tff(c_4128,plain,(
    ! [A_982] :
      ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9(A_982,'#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9(A_982,'#skF_6','#skF_7'))
      | ~ v1_relat_1(u1_orders_2('#skF_6'))
      | ~ l1_orders_2(k4_waybel_9(A_982,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_982)
      | ~ l1_struct_0(A_982)
      | v2_struct_0(A_982) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4127])).

tff(c_4133,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4128])).

tff(c_4136,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_131,c_4133])).

tff(c_4140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4136])).

tff(c_4214,plain,(
    ! [A_1658] :
      ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9(A_1658,'#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9(A_1658,'#skF_6','#skF_7'))
      | ~ l1_orders_2(k4_waybel_9(A_1658,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_1658)
      | ~ l1_struct_0(A_1658)
      | v2_struct_0(A_1658) ) ),
    inference(splitRight,[status(thm)],[c_4128])).

tff(c_20,plain,(
    ! [B_19,A_17] :
      ( v4_yellow_0(B_19,A_17)
      | k1_toler_1(u1_orders_2(A_17),u1_struct_0(B_19)) != u1_orders_2(B_19)
      | ~ m1_yellow_0(B_19,A_17)
      | ~ l1_orders_2(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4374,plain,(
    ! [A_1658] :
      ( v4_yellow_0(k4_waybel_9(A_1658,'#skF_6','#skF_7'),'#skF_6')
      | ~ m1_yellow_0(k4_waybel_9(A_1658,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_orders_2('#skF_6')
      | ~ l1_orders_2(k4_waybel_9(A_1658,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_1658)
      | ~ l1_struct_0(A_1658)
      | v2_struct_0(A_1658) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4214,c_20])).

tff(c_4549,plain,(
    ! [A_1665] :
      ( v4_yellow_0(k4_waybel_9(A_1665,'#skF_6','#skF_7'),'#skF_6')
      | ~ m1_yellow_0(k4_waybel_9(A_1665,'#skF_6','#skF_7'),'#skF_6')
      | ~ l1_orders_2(k4_waybel_9(A_1665,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_1665)
      | ~ l1_struct_0(A_1665)
      | v2_struct_0(A_1665) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_4374])).

tff(c_2451,plain,(
    ~ v4_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2423])).

tff(c_4624,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4549,c_2451])).

tff(c_4737,plain,
    ( ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_2452,c_4624])).

tff(c_4738,plain,(
    ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4737])).

tff(c_4744,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_2464,c_4738])).

tff(c_4747,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_4744])).

tff(c_4749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_4747])).

tff(c_4750,plain,(
    ~ m1_yellow_6(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_5352,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5346,c_4750])).

tff(c_5356,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_5352])).

tff(c_5357,plain,
    ( ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_5356])).

tff(c_5358,plain,(
    ~ v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5357])).

tff(c_5361,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_5358])).

tff(c_5364,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_5361])).

tff(c_5366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_5364])).

tff(c_5367,plain,
    ( ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5357])).

tff(c_5376,plain,(
    ~ m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5367])).

tff(c_4900,plain,(
    ! [A_1726] :
      ( l1_waybel_0(k4_waybel_9(A_1726,'#skF_6','#skF_7'),A_1726)
      | ~ l1_waybel_0('#skF_6',A_1726)
      | ~ l1_struct_0(A_1726)
      | v2_struct_0(A_1726) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4896])).

tff(c_4904,plain,(
    ! [A_1726] :
      ( l1_orders_2(k4_waybel_9(A_1726,'#skF_6','#skF_7'))
      | ~ l1_waybel_0('#skF_6',A_1726)
      | ~ l1_struct_0(A_1726)
      | v2_struct_0(A_1726) ) ),
    inference(resolution,[status(thm)],[c_4900,c_28])).

tff(c_5368,plain,(
    v6_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5357])).

tff(c_5207,plain,(
    ! [A_1849,B_1850,C_1851] :
      ( r2_relset_1(u1_struct_0(k4_waybel_9(A_1849,B_1850,C_1851)),u1_struct_0(k4_waybel_9(A_1849,B_1850,C_1851)),u1_orders_2(k4_waybel_9(A_1849,B_1850,C_1851)),k1_toler_1(u1_orders_2(B_1850),u1_struct_0(k4_waybel_9(A_1849,B_1850,C_1851))))
      | ~ l1_waybel_0(k4_waybel_9(A_1849,B_1850,C_1851),A_1849)
      | ~ v6_waybel_0(k4_waybel_9(A_1849,B_1850,C_1851),A_1849)
      | ~ m1_subset_1(C_1851,u1_struct_0(B_1850))
      | ~ l1_waybel_0(B_1850,A_1849)
      | v2_struct_0(B_1850)
      | ~ l1_struct_0(A_1849)
      | v2_struct_0(A_1849) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_5948,plain,(
    ! [B_2183,A_2184,C_2185] :
      ( k1_toler_1(u1_orders_2(B_2183),u1_struct_0(k4_waybel_9(A_2184,B_2183,C_2185))) = u1_orders_2(k4_waybel_9(A_2184,B_2183,C_2185))
      | ~ m1_subset_1(k1_toler_1(u1_orders_2(B_2183),u1_struct_0(k4_waybel_9(A_2184,B_2183,C_2185))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_2184,B_2183,C_2185)),u1_struct_0(k4_waybel_9(A_2184,B_2183,C_2185)))))
      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(A_2184,B_2183,C_2185)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_2184,B_2183,C_2185)),u1_struct_0(k4_waybel_9(A_2184,B_2183,C_2185)))))
      | ~ l1_waybel_0(k4_waybel_9(A_2184,B_2183,C_2185),A_2184)
      | ~ v6_waybel_0(k4_waybel_9(A_2184,B_2183,C_2185),A_2184)
      | ~ m1_subset_1(C_2185,u1_struct_0(B_2183))
      | ~ l1_waybel_0(B_2183,A_2184)
      | v2_struct_0(B_2183)
      | ~ l1_struct_0(A_2184)
      | v2_struct_0(A_2184) ) ),
    inference(resolution,[status(thm)],[c_5207,c_10])).

tff(c_6498,plain,(
    ! [B_2340,A_2341,C_2342] :
      ( k1_toler_1(u1_orders_2(B_2340),u1_struct_0(k4_waybel_9(A_2341,B_2340,C_2342))) = u1_orders_2(k4_waybel_9(A_2341,B_2340,C_2342))
      | ~ m1_subset_1(u1_orders_2(k4_waybel_9(A_2341,B_2340,C_2342)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_2341,B_2340,C_2342)),u1_struct_0(k4_waybel_9(A_2341,B_2340,C_2342)))))
      | ~ l1_waybel_0(k4_waybel_9(A_2341,B_2340,C_2342),A_2341)
      | ~ v6_waybel_0(k4_waybel_9(A_2341,B_2340,C_2342),A_2341)
      | ~ m1_subset_1(C_2342,u1_struct_0(B_2340))
      | ~ l1_waybel_0(B_2340,A_2341)
      | v2_struct_0(B_2340)
      | ~ l1_struct_0(A_2341)
      | v2_struct_0(A_2341)
      | ~ v1_relat_1(u1_orders_2(B_2340)) ) ),
    inference(resolution,[status(thm)],[c_24,c_5948])).

tff(c_6547,plain,(
    ! [B_2373,A_2374,C_2375] :
      ( k1_toler_1(u1_orders_2(B_2373),u1_struct_0(k4_waybel_9(A_2374,B_2373,C_2375))) = u1_orders_2(k4_waybel_9(A_2374,B_2373,C_2375))
      | ~ l1_waybel_0(k4_waybel_9(A_2374,B_2373,C_2375),A_2374)
      | ~ v6_waybel_0(k4_waybel_9(A_2374,B_2373,C_2375),A_2374)
      | ~ m1_subset_1(C_2375,u1_struct_0(B_2373))
      | ~ l1_waybel_0(B_2373,A_2374)
      | v2_struct_0(B_2373)
      | ~ l1_struct_0(A_2374)
      | v2_struct_0(A_2374)
      | ~ v1_relat_1(u1_orders_2(B_2373))
      | ~ l1_orders_2(k4_waybel_9(A_2374,B_2373,C_2375)) ) ),
    inference(resolution,[status(thm)],[c_12,c_6498])).

tff(c_6549,plain,
    ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5368,c_6547])).

tff(c_6554,plain,
    ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_6549])).

tff(c_6555,plain,
    ( k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_6554])).

tff(c_6557,plain,(
    ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_6555])).

tff(c_6576,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4904,c_6557])).

tff(c_6579,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_6576])).

tff(c_6581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6579])).

tff(c_6583,plain,(
    l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6555])).

tff(c_4775,plain,(
    ! [A_1677] :
      ( m1_subset_1(u1_orders_2(A_1677),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1677),u1_struct_0(A_1677))))
      | ~ l1_orders_2(A_1677) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4779,plain,(
    ! [A_1677] :
      ( v1_relat_1(u1_orders_2(A_1677))
      | ~ l1_orders_2(A_1677) ) ),
    inference(resolution,[status(thm)],[c_4775,c_6])).

tff(c_6582,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5')
    | k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6555])).

tff(c_6584,plain,(
    ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6582])).

tff(c_6587,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4899,c_6584])).

tff(c_6590,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_6587])).

tff(c_6592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_6590])).

tff(c_6593,plain,
    ( ~ v1_relat_1(u1_orders_2('#skF_6'))
    | k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6582])).

tff(c_6633,plain,(
    ~ v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6593])).

tff(c_6636,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_4779,c_6633])).

tff(c_6640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6636])).

tff(c_6642,plain,(
    v1_relat_1(u1_orders_2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_6593])).

tff(c_6641,plain,(
    k1_toler_1(u1_orders_2('#skF_6'),u1_struct_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'))) = u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6593])).

tff(c_4780,plain,(
    ! [A_1678] :
      ( v1_relat_1(u1_orders_2(A_1678))
      | ~ l1_orders_2(A_1678) ) ),
    inference(resolution,[status(thm)],[c_4775,c_6])).

tff(c_4791,plain,(
    ! [A_1682,B_1683] :
      ( k2_wellord1(u1_orders_2(A_1682),B_1683) = k1_toler_1(u1_orders_2(A_1682),B_1683)
      | ~ l1_orders_2(A_1682) ) ),
    inference(resolution,[status(thm)],[c_4780,c_26])).

tff(c_4762,plain,(
    ! [A_1673,B_1674] :
      ( k3_xboole_0(A_1673,k2_zfmisc_1(B_1674,B_1674)) = k2_wellord1(A_1673,B_1674)
      | ~ v1_relat_1(A_1673) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4768,plain,(
    ! [A_1673,B_1674] :
      ( r1_tarski(k2_wellord1(A_1673,B_1674),A_1673)
      | ~ v1_relat_1(A_1673) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4762,c_2])).

tff(c_4797,plain,(
    ! [A_1682,B_1683] :
      ( r1_tarski(k1_toler_1(u1_orders_2(A_1682),B_1683),u1_orders_2(A_1682))
      | ~ v1_relat_1(u1_orders_2(A_1682))
      | ~ l1_orders_2(A_1682) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4791,c_4768])).

tff(c_6885,plain,
    ( r1_tarski(u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')),u1_orders_2('#skF_6'))
    | ~ v1_relat_1(u1_orders_2('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6641,c_4797])).

tff(c_7017,plain,(
    r1_tarski(u1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7')),u1_orders_2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_6642,c_6885])).

tff(c_4921,plain,(
    ! [A_1739,B_1740,C_1741] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(A_1739,B_1740,C_1741)),u1_struct_0(B_1740))
      | ~ m1_subset_1(C_1741,u1_struct_0(B_1740))
      | ~ l1_waybel_0(B_1740,A_1739)
      | v2_struct_0(B_1740)
      | ~ l1_struct_0(A_1739)
      | v2_struct_0(A_1739) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_4925,plain,(
    ! [A_1739,B_1740,C_1741] :
      ( m1_yellow_0(k4_waybel_9(A_1739,B_1740,C_1741),B_1740)
      | ~ r1_tarski(u1_orders_2(k4_waybel_9(A_1739,B_1740,C_1741)),u1_orders_2(B_1740))
      | ~ l1_orders_2(k4_waybel_9(A_1739,B_1740,C_1741))
      | ~ l1_orders_2(B_1740)
      | ~ m1_subset_1(C_1741,u1_struct_0(B_1740))
      | ~ l1_waybel_0(B_1740,A_1739)
      | v2_struct_0(B_1740)
      | ~ l1_struct_0(A_1739)
      | v2_struct_0(A_1739) ) ),
    inference(resolution,[status(thm)],[c_4921,c_14])).

tff(c_7048,plain,
    ( m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | ~ l1_orders_2(k4_waybel_9('#skF_5','#skF_6','#skF_7'))
    | ~ l1_orders_2('#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_7017,c_4925])).

tff(c_7051,plain,
    ( m1_yellow_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_94,c_6583,c_7048])).

tff(c_7053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_82,c_5376,c_7051])).

tff(c_7054,plain,(
    ~ l1_waybel_0(k4_waybel_9('#skF_5','#skF_6','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_5367])).

tff(c_7058,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4899,c_7054])).

tff(c_7061,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_7058])).

tff(c_7063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_7061])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/4.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/4.08  
% 10.54/4.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.54/4.08  %$ r2_relset_1 > v2_yellow_6 > r1_orders_2 > m1_yellow_6 > v6_waybel_0 > v4_yellow_0 > r2_hidden > r1_tarski > m1_yellow_0 > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_relat_1 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_1 > #skF_3
% 10.54/4.08  
% 10.54/4.08  %Foreground sorts:
% 10.54/4.08  
% 10.54/4.08  
% 10.54/4.08  %Background operators:
% 10.54/4.08  
% 10.54/4.08  
% 10.54/4.08  %Foreground operators:
% 10.54/4.08  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.54/4.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.54/4.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.54/4.08  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 10.54/4.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.54/4.08  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.54/4.08  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 10.54/4.08  tff(v4_yellow_0, type, v4_yellow_0: ($i * $i) > $o).
% 10.54/4.08  tff(k1_toler_1, type, k1_toler_1: ($i * $i) > $i).
% 10.54/4.08  tff('#skF_7', type, '#skF_7': $i).
% 10.54/4.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.54/4.08  tff('#skF_5', type, '#skF_5': $i).
% 10.54/4.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.54/4.08  tff('#skF_6', type, '#skF_6': $i).
% 10.54/4.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.54/4.08  tff(m1_yellow_0, type, m1_yellow_0: ($i * $i) > $o).
% 10.54/4.08  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.54/4.08  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 10.54/4.08  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.54/4.08  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 10.54/4.08  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 10.54/4.08  tff(m1_yellow_6, type, m1_yellow_6: ($i * $i * $i) > $o).
% 10.54/4.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.54/4.08  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 10.54/4.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.54/4.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.54/4.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.54/4.08  tff(v2_yellow_6, type, v2_yellow_6: ($i * $i * $i) > $o).
% 10.54/4.08  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 10.54/4.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.54/4.08  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.54/4.08  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 10.54/4.08  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 10.54/4.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.54/4.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.54/4.08  
% 10.69/4.11  tff(f_197, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (v2_yellow_6(k4_waybel_9(A, B, C), A, B) & m1_yellow_6(k4_waybel_9(A, B, C), A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_waybel_9)).
% 10.69/4.11  tff(f_162, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k4_waybel_9(A, B, C), A) & l1_waybel_0(k4_waybel_9(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 10.69/4.11  tff(f_146, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k4_waybel_9(A, B, C)) <=> (((![E]: (r2_hidden(E, u1_struct_0(D)) <=> (?[F]: ((m1_subset_1(F, u1_struct_0(B)) & (F = E)) & r1_orders_2(B, C, F))))) & r2_relset_1(u1_struct_0(D), u1_struct_0(D), u1_orders_2(D), k1_toler_1(u1_orders_2(B), u1_struct_0(D)))) & (u1_waybel_0(A, D) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 10.69/4.11  tff(f_97, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (l1_waybel_0(C, A) => (m1_yellow_6(C, A, B) <=> (m1_yellow_0(C, B) & (u1_waybel_0(A, C) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_yellow_6)).
% 10.69/4.11  tff(f_83, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 10.69/4.11  tff(f_111, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => (![C]: (m1_yellow_6(C, A, B) => (v2_yellow_6(C, A, B) <=> (v4_yellow_0(C, B) & m1_yellow_0(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_6)).
% 10.69/4.11  tff(f_48, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(u1_orders_2(A), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 10.69/4.11  tff(f_72, axiom, (![A, B]: (v1_relat_1(A) => m1_subset_1(k1_toler_1(A, B), k1_zfmisc_1(k2_zfmisc_1(B, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_toler_1)).
% 10.69/4.11  tff(f_44, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.69/4.11  tff(f_36, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.69/4.11  tff(f_76, axiom, (![A, B]: (v1_relat_1(A) => (k1_toler_1(A, B) = k2_wellord1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_toler_1)).
% 10.69/4.11  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 10.69/4.11  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.69/4.11  tff(f_178, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 10.69/4.11  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_orders_2(B) => (m1_yellow_0(B, A) <=> (r1_tarski(u1_struct_0(B), u1_struct_0(A)) & r1_tarski(u1_orders_2(B), u1_orders_2(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_yellow_0)).
% 10.69/4.11  tff(f_68, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_yellow_0(B, A) => (v4_yellow_0(B, A) <=> (u1_orders_2(B) = k1_toler_1(u1_orders_2(A), u1_struct_0(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_yellow_0)).
% 10.69/4.11  tff(c_86, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.69/4.11  tff(c_84, plain, (l1_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.69/4.11  tff(c_80, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.69/4.11  tff(c_82, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.69/4.11  tff(c_78, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.69/4.11  tff(c_4894, plain, (![A_1723, B_1724, C_1725]: (l1_waybel_0(k4_waybel_9(A_1723, B_1724, C_1725), A_1723) | ~m1_subset_1(C_1725, u1_struct_0(B_1724)) | ~l1_waybel_0(B_1724, A_1723) | v2_struct_0(B_1724) | ~l1_struct_0(A_1723) | v2_struct_0(A_1723))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.69/4.11  tff(c_4896, plain, (![A_1723]: (l1_waybel_0(k4_waybel_9(A_1723, '#skF_6', '#skF_7'), A_1723) | ~l1_waybel_0('#skF_6', A_1723) | v2_struct_0('#skF_6') | ~l1_struct_0(A_1723) | v2_struct_0(A_1723))), inference(resolution, [status(thm)], [c_78, c_4894])).
% 10.69/4.11  tff(c_4899, plain, (![A_1723]: (l1_waybel_0(k4_waybel_9(A_1723, '#skF_6', '#skF_7'), A_1723) | ~l1_waybel_0('#skF_6', A_1723) | ~l1_struct_0(A_1723) | v2_struct_0(A_1723))), inference(negUnitSimplification, [status(thm)], [c_82, c_4896])).
% 10.69/4.11  tff(c_72, plain, (![A_213, B_214, C_215]: (v6_waybel_0(k4_waybel_9(A_213, B_214, C_215), A_213) | ~m1_subset_1(C_215, u1_struct_0(B_214)) | ~l1_waybel_0(B_214, A_213) | v2_struct_0(B_214) | ~l1_struct_0(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.69/4.11  tff(c_5137, plain, (![B_1830, A_1831, C_1832]: (k2_partfun1(u1_struct_0(B_1830), u1_struct_0(A_1831), u1_waybel_0(A_1831, B_1830), u1_struct_0(k4_waybel_9(A_1831, B_1830, C_1832)))=u1_waybel_0(A_1831, k4_waybel_9(A_1831, B_1830, C_1832)) | ~l1_waybel_0(k4_waybel_9(A_1831, B_1830, C_1832), A_1831) | ~v6_waybel_0(k4_waybel_9(A_1831, B_1830, C_1832), A_1831) | ~m1_subset_1(C_1832, u1_struct_0(B_1830)) | ~l1_waybel_0(B_1830, A_1831) | v2_struct_0(B_1830) | ~l1_struct_0(A_1831) | v2_struct_0(A_1831))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.69/4.11  tff(c_30, plain, (![C_33, A_27, B_31]: (m1_yellow_6(C_33, A_27, B_31) | k2_partfun1(u1_struct_0(B_31), u1_struct_0(A_27), u1_waybel_0(A_27, B_31), u1_struct_0(C_33))!=u1_waybel_0(A_27, C_33) | ~m1_yellow_0(C_33, B_31) | ~l1_waybel_0(C_33, A_27) | ~l1_waybel_0(B_31, A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.69/4.11  tff(c_5346, plain, (![A_1914, B_1915, C_1916]: (m1_yellow_6(k4_waybel_9(A_1914, B_1915, C_1916), A_1914, B_1915) | ~m1_yellow_0(k4_waybel_9(A_1914, B_1915, C_1916), B_1915) | ~l1_waybel_0(k4_waybel_9(A_1914, B_1915, C_1916), A_1914) | ~v6_waybel_0(k4_waybel_9(A_1914, B_1915, C_1916), A_1914) | ~m1_subset_1(C_1916, u1_struct_0(B_1915)) | ~l1_waybel_0(B_1915, A_1914) | v2_struct_0(B_1915) | ~l1_struct_0(A_1914) | v2_struct_0(A_1914))), inference(superposition, [status(thm), theory('equality')], [c_5137, c_30])).
% 10.69/4.11  tff(c_2453, plain, (![A_982, B_983, C_984]: (l1_waybel_0(k4_waybel_9(A_982, B_983, C_984), A_982) | ~m1_subset_1(C_984, u1_struct_0(B_983)) | ~l1_waybel_0(B_983, A_982) | v2_struct_0(B_983) | ~l1_struct_0(A_982) | v2_struct_0(A_982))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.69/4.11  tff(c_2455, plain, (![A_982]: (l1_waybel_0(k4_waybel_9(A_982, '#skF_6', '#skF_7'), A_982) | ~l1_waybel_0('#skF_6', A_982) | v2_struct_0('#skF_6') | ~l1_struct_0(A_982) | v2_struct_0(A_982))), inference(resolution, [status(thm)], [c_78, c_2453])).
% 10.69/4.11  tff(c_2460, plain, (![A_985]: (l1_waybel_0(k4_waybel_9(A_985, '#skF_6', '#skF_7'), A_985) | ~l1_waybel_0('#skF_6', A_985) | ~l1_struct_0(A_985) | v2_struct_0(A_985))), inference(negUnitSimplification, [status(thm)], [c_82, c_2455])).
% 10.69/4.11  tff(c_28, plain, (![B_26, A_24]: (l1_orders_2(B_26) | ~l1_waybel_0(B_26, A_24) | ~l1_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.69/4.11  tff(c_2464, plain, (![A_985]: (l1_orders_2(k4_waybel_9(A_985, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_985) | ~l1_struct_0(A_985) | v2_struct_0(A_985))), inference(resolution, [status(thm)], [c_2460, c_28])).
% 10.69/4.11  tff(c_2433, plain, (![A_978, B_979, C_980]: (l1_waybel_0(k4_waybel_9(A_978, B_979, C_980), A_978) | ~m1_subset_1(C_980, u1_struct_0(B_979)) | ~l1_waybel_0(B_979, A_978) | v2_struct_0(B_979) | ~l1_struct_0(A_978) | v2_struct_0(A_978))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.69/4.11  tff(c_2435, plain, (![A_978]: (l1_waybel_0(k4_waybel_9(A_978, '#skF_6', '#skF_7'), A_978) | ~l1_waybel_0('#skF_6', A_978) | v2_struct_0('#skF_6') | ~l1_struct_0(A_978) | v2_struct_0(A_978))), inference(resolution, [status(thm)], [c_78, c_2433])).
% 10.69/4.11  tff(c_2439, plain, (![A_981]: (l1_waybel_0(k4_waybel_9(A_981, '#skF_6', '#skF_7'), A_981) | ~l1_waybel_0('#skF_6', A_981) | ~l1_struct_0(A_981) | v2_struct_0(A_981))), inference(negUnitSimplification, [status(thm)], [c_82, c_2435])).
% 10.69/4.11  tff(c_244, plain, (![A_297, B_298, C_299]: (l1_waybel_0(k4_waybel_9(A_297, B_298, C_299), A_297) | ~m1_subset_1(C_299, u1_struct_0(B_298)) | ~l1_waybel_0(B_298, A_297) | v2_struct_0(B_298) | ~l1_struct_0(A_297) | v2_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.69/4.11  tff(c_246, plain, (![A_297]: (l1_waybel_0(k4_waybel_9(A_297, '#skF_6', '#skF_7'), A_297) | ~l1_waybel_0('#skF_6', A_297) | v2_struct_0('#skF_6') | ~l1_struct_0(A_297) | v2_struct_0(A_297))), inference(resolution, [status(thm)], [c_78, c_244])).
% 10.69/4.11  tff(c_249, plain, (![A_297]: (l1_waybel_0(k4_waybel_9(A_297, '#skF_6', '#skF_7'), A_297) | ~l1_waybel_0('#skF_6', A_297) | ~l1_struct_0(A_297) | v2_struct_0(A_297))), inference(negUnitSimplification, [status(thm)], [c_82, c_246])).
% 10.69/4.11  tff(c_408, plain, (![B_367, A_368, C_369]: (k2_partfun1(u1_struct_0(B_367), u1_struct_0(A_368), u1_waybel_0(A_368, B_367), u1_struct_0(k4_waybel_9(A_368, B_367, C_369)))=u1_waybel_0(A_368, k4_waybel_9(A_368, B_367, C_369)) | ~l1_waybel_0(k4_waybel_9(A_368, B_367, C_369), A_368) | ~v6_waybel_0(k4_waybel_9(A_368, B_367, C_369), A_368) | ~m1_subset_1(C_369, u1_struct_0(B_367)) | ~l1_waybel_0(B_367, A_368) | v2_struct_0(B_367) | ~l1_struct_0(A_368) | v2_struct_0(A_368))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.69/4.11  tff(c_686, plain, (![A_481, B_482, C_483]: (m1_yellow_6(k4_waybel_9(A_481, B_482, C_483), A_481, B_482) | ~m1_yellow_0(k4_waybel_9(A_481, B_482, C_483), B_482) | ~l1_waybel_0(k4_waybel_9(A_481, B_482, C_483), A_481) | ~v6_waybel_0(k4_waybel_9(A_481, B_482, C_483), A_481) | ~m1_subset_1(C_483, u1_struct_0(B_482)) | ~l1_waybel_0(B_482, A_481) | v2_struct_0(B_482) | ~l1_struct_0(A_481) | v2_struct_0(A_481))), inference(superposition, [status(thm), theory('equality')], [c_408, c_30])).
% 10.69/4.11  tff(c_227, plain, (![C_291, A_292, B_293]: (v2_yellow_6(C_291, A_292, B_293) | ~m1_yellow_0(C_291, B_293) | ~v4_yellow_0(C_291, B_293) | ~m1_yellow_6(C_291, A_292, B_293) | ~l1_waybel_0(B_293, A_292) | ~l1_struct_0(A_292))), inference(cnfTransformation, [status(thm)], [f_111])).
% 10.69/4.11  tff(c_76, plain, (~m1_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6') | ~v2_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_197])).
% 10.69/4.11  tff(c_96, plain, (~v2_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_76])).
% 10.69/4.11  tff(c_236, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~v4_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~m1_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6') | ~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_227, c_96])).
% 10.69/4.11  tff(c_241, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~v4_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~m1_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_236])).
% 10.69/4.11  tff(c_243, plain, (~m1_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_241])).
% 10.69/4.11  tff(c_689, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_686, c_243])).
% 10.69/4.11  tff(c_695, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_689])).
% 10.69/4.11  tff(c_696, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_695])).
% 10.69/4.11  tff(c_698, plain, (~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_696])).
% 10.69/4.11  tff(c_701, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_698])).
% 10.69/4.11  tff(c_704, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_701])).
% 10.69/4.11  tff(c_706, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_704])).
% 10.69/4.11  tff(c_707, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_696])).
% 10.69/4.11  tff(c_716, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_707])).
% 10.69/4.11  tff(c_88, plain, (![B_229, A_230]: (l1_orders_2(B_229) | ~l1_waybel_0(B_229, A_230) | ~l1_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.69/4.11  tff(c_91, plain, (l1_orders_2('#skF_6') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_88])).
% 10.69/4.11  tff(c_94, plain, (l1_orders_2('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_91])).
% 10.69/4.11  tff(c_250, plain, (![A_300]: (l1_waybel_0(k4_waybel_9(A_300, '#skF_6', '#skF_7'), A_300) | ~l1_waybel_0('#skF_6', A_300) | ~l1_struct_0(A_300) | v2_struct_0(A_300))), inference(negUnitSimplification, [status(thm)], [c_82, c_246])).
% 10.69/4.11  tff(c_254, plain, (![A_300]: (l1_orders_2(k4_waybel_9(A_300, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_300) | ~l1_struct_0(A_300) | v2_struct_0(A_300))), inference(resolution, [status(thm)], [c_250, c_28])).
% 10.69/4.11  tff(c_708, plain, (v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_696])).
% 10.69/4.11  tff(c_12, plain, (![A_13]: (m1_subset_1(u1_orders_2(A_13), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_13), u1_struct_0(A_13)))) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.69/4.11  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(k1_toler_1(A_20, B_21), k1_zfmisc_1(k2_zfmisc_1(B_21, B_21))) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.69/4.11  tff(c_540, plain, (![A_412, B_413, C_414]: (r2_relset_1(u1_struct_0(k4_waybel_9(A_412, B_413, C_414)), u1_struct_0(k4_waybel_9(A_412, B_413, C_414)), u1_orders_2(k4_waybel_9(A_412, B_413, C_414)), k1_toler_1(u1_orders_2(B_413), u1_struct_0(k4_waybel_9(A_412, B_413, C_414)))) | ~l1_waybel_0(k4_waybel_9(A_412, B_413, C_414), A_412) | ~v6_waybel_0(k4_waybel_9(A_412, B_413, C_414), A_412) | ~m1_subset_1(C_414, u1_struct_0(B_413)) | ~l1_waybel_0(B_413, A_412) | v2_struct_0(B_413) | ~l1_struct_0(A_412) | v2_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.69/4.11  tff(c_10, plain, (![D_12, C_11, A_9, B_10]: (D_12=C_11 | ~r2_relset_1(A_9, B_10, C_11, D_12) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.69/4.11  tff(c_1281, plain, (![B_746, A_747, C_748]: (k1_toler_1(u1_orders_2(B_746), u1_struct_0(k4_waybel_9(A_747, B_746, C_748)))=u1_orders_2(k4_waybel_9(A_747, B_746, C_748)) | ~m1_subset_1(k1_toler_1(u1_orders_2(B_746), u1_struct_0(k4_waybel_9(A_747, B_746, C_748))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_747, B_746, C_748)), u1_struct_0(k4_waybel_9(A_747, B_746, C_748))))) | ~m1_subset_1(u1_orders_2(k4_waybel_9(A_747, B_746, C_748)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_747, B_746, C_748)), u1_struct_0(k4_waybel_9(A_747, B_746, C_748))))) | ~l1_waybel_0(k4_waybel_9(A_747, B_746, C_748), A_747) | ~v6_waybel_0(k4_waybel_9(A_747, B_746, C_748), A_747) | ~m1_subset_1(C_748, u1_struct_0(B_746)) | ~l1_waybel_0(B_746, A_747) | v2_struct_0(B_746) | ~l1_struct_0(A_747) | v2_struct_0(A_747))), inference(resolution, [status(thm)], [c_540, c_10])).
% 10.69/4.11  tff(c_1757, plain, (![B_903, A_904, C_905]: (k1_toler_1(u1_orders_2(B_903), u1_struct_0(k4_waybel_9(A_904, B_903, C_905)))=u1_orders_2(k4_waybel_9(A_904, B_903, C_905)) | ~m1_subset_1(u1_orders_2(k4_waybel_9(A_904, B_903, C_905)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_904, B_903, C_905)), u1_struct_0(k4_waybel_9(A_904, B_903, C_905))))) | ~l1_waybel_0(k4_waybel_9(A_904, B_903, C_905), A_904) | ~v6_waybel_0(k4_waybel_9(A_904, B_903, C_905), A_904) | ~m1_subset_1(C_905, u1_struct_0(B_903)) | ~l1_waybel_0(B_903, A_904) | v2_struct_0(B_903) | ~l1_struct_0(A_904) | v2_struct_0(A_904) | ~v1_relat_1(u1_orders_2(B_903)))), inference(resolution, [status(thm)], [c_24, c_1281])).
% 10.69/4.11  tff(c_1920, plain, (![B_958, A_959, C_960]: (k1_toler_1(u1_orders_2(B_958), u1_struct_0(k4_waybel_9(A_959, B_958, C_960)))=u1_orders_2(k4_waybel_9(A_959, B_958, C_960)) | ~l1_waybel_0(k4_waybel_9(A_959, B_958, C_960), A_959) | ~v6_waybel_0(k4_waybel_9(A_959, B_958, C_960), A_959) | ~m1_subset_1(C_960, u1_struct_0(B_958)) | ~l1_waybel_0(B_958, A_959) | v2_struct_0(B_958) | ~l1_struct_0(A_959) | v2_struct_0(A_959) | ~v1_relat_1(u1_orders_2(B_958)) | ~l1_orders_2(k4_waybel_9(A_959, B_958, C_960)))), inference(resolution, [status(thm)], [c_12, c_1757])).
% 10.69/4.11  tff(c_1922, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_708, c_1920])).
% 10.69/4.11  tff(c_1927, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_1922])).
% 10.69/4.11  tff(c_1928, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_1927])).
% 10.69/4.11  tff(c_1930, plain, (~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_1928])).
% 10.69/4.11  tff(c_1937, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_254, c_1930])).
% 10.69/4.11  tff(c_1940, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_1937])).
% 10.69/4.11  tff(c_1942, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_1940])).
% 10.69/4.11  tff(c_1944, plain, (l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1928])).
% 10.69/4.11  tff(c_124, plain, (![A_247]: (m1_subset_1(u1_orders_2(A_247), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_247), u1_struct_0(A_247)))) | ~l1_orders_2(A_247))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.69/4.11  tff(c_6, plain, (![C_8, A_6, B_7]: (v1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.69/4.11  tff(c_131, plain, (![A_247]: (v1_relat_1(u1_orders_2(A_247)) | ~l1_orders_2(A_247))), inference(resolution, [status(thm)], [c_124, c_6])).
% 10.69/4.11  tff(c_1943, plain, (~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1928])).
% 10.69/4.11  tff(c_1945, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1943])).
% 10.69/4.11  tff(c_1949, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_249, c_1945])).
% 10.69/4.11  tff(c_1952, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_1949])).
% 10.69/4.11  tff(c_1954, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_1952])).
% 10.69/4.11  tff(c_1955, plain, (~v1_relat_1(u1_orders_2('#skF_6')) | k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1943])).
% 10.69/4.11  tff(c_1991, plain, (~v1_relat_1(u1_orders_2('#skF_6'))), inference(splitLeft, [status(thm)], [c_1955])).
% 10.69/4.11  tff(c_1994, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_131, c_1991])).
% 10.69/4.11  tff(c_1998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_1994])).
% 10.69/4.11  tff(c_2000, plain, (v1_relat_1(u1_orders_2('#skF_6'))), inference(splitRight, [status(thm)], [c_1955])).
% 10.69/4.11  tff(c_1999, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_1955])).
% 10.69/4.11  tff(c_132, plain, (![A_248]: (v1_relat_1(u1_orders_2(A_248)) | ~l1_orders_2(A_248))), inference(resolution, [status(thm)], [c_124, c_6])).
% 10.69/4.11  tff(c_26, plain, (![A_22, B_23]: (k2_wellord1(A_22, B_23)=k1_toler_1(A_22, B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_76])).
% 10.69/4.11  tff(c_137, plain, (![A_251, B_252]: (k2_wellord1(u1_orders_2(A_251), B_252)=k1_toler_1(u1_orders_2(A_251), B_252) | ~l1_orders_2(A_251))), inference(resolution, [status(thm)], [c_132, c_26])).
% 10.69/4.11  tff(c_98, plain, (![A_236, B_237]: (k3_xboole_0(A_236, k2_zfmisc_1(B_237, B_237))=k2_wellord1(A_236, B_237) | ~v1_relat_1(A_236))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.69/4.11  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.69/4.11  tff(c_104, plain, (![A_236, B_237]: (r1_tarski(k2_wellord1(A_236, B_237), A_236) | ~v1_relat_1(A_236))), inference(superposition, [status(thm), theory('equality')], [c_98, c_2])).
% 10.69/4.11  tff(c_143, plain, (![A_251, B_252]: (r1_tarski(k1_toler_1(u1_orders_2(A_251), B_252), u1_orders_2(A_251)) | ~v1_relat_1(u1_orders_2(A_251)) | ~l1_orders_2(A_251))), inference(superposition, [status(thm), theory('equality')], [c_137, c_104])).
% 10.69/4.11  tff(c_2247, plain, (r1_tarski(u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')), u1_orders_2('#skF_6')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1999, c_143])).
% 10.69/4.11  tff(c_2379, plain, (r1_tarski(u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')), u1_orders_2('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2000, c_2247])).
% 10.69/4.11  tff(c_260, plain, (![A_304, B_305, C_306]: (r1_tarski(u1_struct_0(k4_waybel_9(A_304, B_305, C_306)), u1_struct_0(B_305)) | ~m1_subset_1(C_306, u1_struct_0(B_305)) | ~l1_waybel_0(B_305, A_304) | v2_struct_0(B_305) | ~l1_struct_0(A_304) | v2_struct_0(A_304))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.69/4.11  tff(c_14, plain, (![B_16, A_14]: (m1_yellow_0(B_16, A_14) | ~r1_tarski(u1_orders_2(B_16), u1_orders_2(A_14)) | ~r1_tarski(u1_struct_0(B_16), u1_struct_0(A_14)) | ~l1_orders_2(B_16) | ~l1_orders_2(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.69/4.11  tff(c_264, plain, (![A_304, B_305, C_306]: (m1_yellow_0(k4_waybel_9(A_304, B_305, C_306), B_305) | ~r1_tarski(u1_orders_2(k4_waybel_9(A_304, B_305, C_306)), u1_orders_2(B_305)) | ~l1_orders_2(k4_waybel_9(A_304, B_305, C_306)) | ~l1_orders_2(B_305) | ~m1_subset_1(C_306, u1_struct_0(B_305)) | ~l1_waybel_0(B_305, A_304) | v2_struct_0(B_305) | ~l1_struct_0(A_304) | v2_struct_0(A_304))), inference(resolution, [status(thm)], [c_260, c_14])).
% 10.69/4.11  tff(c_2400, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2379, c_264])).
% 10.69/4.11  tff(c_2403, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_94, c_1944, c_2400])).
% 10.69/4.11  tff(c_2405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_716, c_2403])).
% 10.69/4.11  tff(c_2406, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_707])).
% 10.69/4.11  tff(c_2417, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_249, c_2406])).
% 10.69/4.11  tff(c_2420, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_2417])).
% 10.69/4.11  tff(c_2422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2420])).
% 10.69/4.11  tff(c_2423, plain, (~v4_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_241])).
% 10.69/4.11  tff(c_2431, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_2423])).
% 10.69/4.11  tff(c_2424, plain, (m1_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_241])).
% 10.69/4.11  tff(c_34, plain, (![C_33, B_31, A_27]: (m1_yellow_0(C_33, B_31) | ~m1_yellow_6(C_33, A_27, B_31) | ~l1_waybel_0(C_33, A_27) | ~l1_waybel_0(B_31, A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_97])).
% 10.69/4.11  tff(c_2427, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2424, c_34])).
% 10.69/4.11  tff(c_2430, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_2427])).
% 10.69/4.11  tff(c_2432, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_2431, c_2430])).
% 10.69/4.11  tff(c_2442, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2439, c_2432])).
% 10.69/4.11  tff(c_2448, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_2442])).
% 10.69/4.11  tff(c_2450, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_2448])).
% 10.69/4.11  tff(c_2452, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_2423])).
% 10.69/4.11  tff(c_2458, plain, (![A_982]: (l1_waybel_0(k4_waybel_9(A_982, '#skF_6', '#skF_7'), A_982) | ~l1_waybel_0('#skF_6', A_982) | ~l1_struct_0(A_982) | v2_struct_0(A_982))), inference(negUnitSimplification, [status(thm)], [c_82, c_2455])).
% 10.69/4.11  tff(c_2739, plain, (![A_1094, B_1095, C_1096]: (r2_relset_1(u1_struct_0(k4_waybel_9(A_1094, B_1095, C_1096)), u1_struct_0(k4_waybel_9(A_1094, B_1095, C_1096)), u1_orders_2(k4_waybel_9(A_1094, B_1095, C_1096)), k1_toler_1(u1_orders_2(B_1095), u1_struct_0(k4_waybel_9(A_1094, B_1095, C_1096)))) | ~l1_waybel_0(k4_waybel_9(A_1094, B_1095, C_1096), A_1094) | ~v6_waybel_0(k4_waybel_9(A_1094, B_1095, C_1096), A_1094) | ~m1_subset_1(C_1096, u1_struct_0(B_1095)) | ~l1_waybel_0(B_1095, A_1094) | v2_struct_0(B_1095) | ~l1_struct_0(A_1094) | v2_struct_0(A_1094))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.69/4.11  tff(c_3479, plain, (![B_1441, A_1442, C_1443]: (k1_toler_1(u1_orders_2(B_1441), u1_struct_0(k4_waybel_9(A_1442, B_1441, C_1443)))=u1_orders_2(k4_waybel_9(A_1442, B_1441, C_1443)) | ~m1_subset_1(k1_toler_1(u1_orders_2(B_1441), u1_struct_0(k4_waybel_9(A_1442, B_1441, C_1443))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_1442, B_1441, C_1443)), u1_struct_0(k4_waybel_9(A_1442, B_1441, C_1443))))) | ~m1_subset_1(u1_orders_2(k4_waybel_9(A_1442, B_1441, C_1443)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_1442, B_1441, C_1443)), u1_struct_0(k4_waybel_9(A_1442, B_1441, C_1443))))) | ~l1_waybel_0(k4_waybel_9(A_1442, B_1441, C_1443), A_1442) | ~v6_waybel_0(k4_waybel_9(A_1442, B_1441, C_1443), A_1442) | ~m1_subset_1(C_1443, u1_struct_0(B_1441)) | ~l1_waybel_0(B_1441, A_1442) | v2_struct_0(B_1441) | ~l1_struct_0(A_1442) | v2_struct_0(A_1442))), inference(resolution, [status(thm)], [c_2739, c_10])).
% 10.69/4.11  tff(c_3947, plain, (![B_1590, A_1591, C_1592]: (k1_toler_1(u1_orders_2(B_1590), u1_struct_0(k4_waybel_9(A_1591, B_1590, C_1592)))=u1_orders_2(k4_waybel_9(A_1591, B_1590, C_1592)) | ~m1_subset_1(u1_orders_2(k4_waybel_9(A_1591, B_1590, C_1592)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_1591, B_1590, C_1592)), u1_struct_0(k4_waybel_9(A_1591, B_1590, C_1592))))) | ~l1_waybel_0(k4_waybel_9(A_1591, B_1590, C_1592), A_1591) | ~v6_waybel_0(k4_waybel_9(A_1591, B_1590, C_1592), A_1591) | ~m1_subset_1(C_1592, u1_struct_0(B_1590)) | ~l1_waybel_0(B_1590, A_1591) | v2_struct_0(B_1590) | ~l1_struct_0(A_1591) | v2_struct_0(A_1591) | ~v1_relat_1(u1_orders_2(B_1590)))), inference(resolution, [status(thm)], [c_24, c_3479])).
% 10.69/4.11  tff(c_4110, plain, (![B_1645, A_1646, C_1647]: (k1_toler_1(u1_orders_2(B_1645), u1_struct_0(k4_waybel_9(A_1646, B_1645, C_1647)))=u1_orders_2(k4_waybel_9(A_1646, B_1645, C_1647)) | ~l1_waybel_0(k4_waybel_9(A_1646, B_1645, C_1647), A_1646) | ~v6_waybel_0(k4_waybel_9(A_1646, B_1645, C_1647), A_1646) | ~m1_subset_1(C_1647, u1_struct_0(B_1645)) | ~l1_waybel_0(B_1645, A_1646) | v2_struct_0(B_1645) | ~l1_struct_0(A_1646) | v2_struct_0(A_1646) | ~v1_relat_1(u1_orders_2(B_1645)) | ~l1_orders_2(k4_waybel_9(A_1646, B_1645, C_1647)))), inference(resolution, [status(thm)], [c_12, c_3947])).
% 10.69/4.11  tff(c_4114, plain, (![B_1648, A_1649, C_1650]: (k1_toler_1(u1_orders_2(B_1648), u1_struct_0(k4_waybel_9(A_1649, B_1648, C_1650)))=u1_orders_2(k4_waybel_9(A_1649, B_1648, C_1650)) | ~l1_waybel_0(k4_waybel_9(A_1649, B_1648, C_1650), A_1649) | ~v1_relat_1(u1_orders_2(B_1648)) | ~l1_orders_2(k4_waybel_9(A_1649, B_1648, C_1650)) | ~m1_subset_1(C_1650, u1_struct_0(B_1648)) | ~l1_waybel_0(B_1648, A_1649) | v2_struct_0(B_1648) | ~l1_struct_0(A_1649) | v2_struct_0(A_1649))), inference(resolution, [status(thm)], [c_72, c_4110])).
% 10.69/4.11  tff(c_4120, plain, (![A_982]: (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9(A_982, '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9(A_982, '#skF_6', '#skF_7')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9(A_982, '#skF_6', '#skF_7')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', A_982) | ~l1_struct_0(A_982) | v2_struct_0(A_982))), inference(resolution, [status(thm)], [c_2458, c_4114])).
% 10.69/4.11  tff(c_4127, plain, (![A_982]: (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9(A_982, '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9(A_982, '#skF_6', '#skF_7')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9(A_982, '#skF_6', '#skF_7')) | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', A_982) | ~l1_struct_0(A_982) | v2_struct_0(A_982))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4120])).
% 10.69/4.11  tff(c_4128, plain, (![A_982]: (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9(A_982, '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9(A_982, '#skF_6', '#skF_7')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9(A_982, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_982) | ~l1_struct_0(A_982) | v2_struct_0(A_982))), inference(negUnitSimplification, [status(thm)], [c_82, c_4127])).
% 10.69/4.11  tff(c_4133, plain, (~v1_relat_1(u1_orders_2('#skF_6'))), inference(splitLeft, [status(thm)], [c_4128])).
% 10.69/4.11  tff(c_4136, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_131, c_4133])).
% 10.69/4.11  tff(c_4140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_4136])).
% 10.69/4.11  tff(c_4214, plain, (![A_1658]: (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9(A_1658, '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9(A_1658, '#skF_6', '#skF_7')) | ~l1_orders_2(k4_waybel_9(A_1658, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_1658) | ~l1_struct_0(A_1658) | v2_struct_0(A_1658))), inference(splitRight, [status(thm)], [c_4128])).
% 10.69/4.11  tff(c_20, plain, (![B_19, A_17]: (v4_yellow_0(B_19, A_17) | k1_toler_1(u1_orders_2(A_17), u1_struct_0(B_19))!=u1_orders_2(B_19) | ~m1_yellow_0(B_19, A_17) | ~l1_orders_2(A_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 10.69/4.11  tff(c_4374, plain, (![A_1658]: (v4_yellow_0(k4_waybel_9(A_1658, '#skF_6', '#skF_7'), '#skF_6') | ~m1_yellow_0(k4_waybel_9(A_1658, '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2('#skF_6') | ~l1_orders_2(k4_waybel_9(A_1658, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_1658) | ~l1_struct_0(A_1658) | v2_struct_0(A_1658))), inference(superposition, [status(thm), theory('equality')], [c_4214, c_20])).
% 10.69/4.11  tff(c_4549, plain, (![A_1665]: (v4_yellow_0(k4_waybel_9(A_1665, '#skF_6', '#skF_7'), '#skF_6') | ~m1_yellow_0(k4_waybel_9(A_1665, '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(k4_waybel_9(A_1665, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_1665) | ~l1_struct_0(A_1665) | v2_struct_0(A_1665))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_4374])).
% 10.69/4.11  tff(c_2451, plain, (~v4_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_2423])).
% 10.69/4.11  tff(c_4624, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4549, c_2451])).
% 10.69/4.11  tff(c_4737, plain, (~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_2452, c_4624])).
% 10.69/4.11  tff(c_4738, plain, (~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_4737])).
% 10.69/4.11  tff(c_4744, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_2464, c_4738])).
% 10.69/4.11  tff(c_4747, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_4744])).
% 10.69/4.11  tff(c_4749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_4747])).
% 10.69/4.11  tff(c_4750, plain, (~m1_yellow_6(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 10.69/4.11  tff(c_5352, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5346, c_4750])).
% 10.69/4.11  tff(c_5356, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_5352])).
% 10.69/4.11  tff(c_5357, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_5356])).
% 10.69/4.11  tff(c_5358, plain, (~v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_5357])).
% 10.69/4.11  tff(c_5361, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_72, c_5358])).
% 10.69/4.11  tff(c_5364, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_5361])).
% 10.69/4.11  tff(c_5366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_5364])).
% 10.69/4.11  tff(c_5367, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_5357])).
% 10.69/4.11  tff(c_5376, plain, (~m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5367])).
% 10.69/4.11  tff(c_4900, plain, (![A_1726]: (l1_waybel_0(k4_waybel_9(A_1726, '#skF_6', '#skF_7'), A_1726) | ~l1_waybel_0('#skF_6', A_1726) | ~l1_struct_0(A_1726) | v2_struct_0(A_1726))), inference(negUnitSimplification, [status(thm)], [c_82, c_4896])).
% 10.69/4.11  tff(c_4904, plain, (![A_1726]: (l1_orders_2(k4_waybel_9(A_1726, '#skF_6', '#skF_7')) | ~l1_waybel_0('#skF_6', A_1726) | ~l1_struct_0(A_1726) | v2_struct_0(A_1726))), inference(resolution, [status(thm)], [c_4900, c_28])).
% 10.69/4.11  tff(c_5368, plain, (v6_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_5357])).
% 10.69/4.11  tff(c_5207, plain, (![A_1849, B_1850, C_1851]: (r2_relset_1(u1_struct_0(k4_waybel_9(A_1849, B_1850, C_1851)), u1_struct_0(k4_waybel_9(A_1849, B_1850, C_1851)), u1_orders_2(k4_waybel_9(A_1849, B_1850, C_1851)), k1_toler_1(u1_orders_2(B_1850), u1_struct_0(k4_waybel_9(A_1849, B_1850, C_1851)))) | ~l1_waybel_0(k4_waybel_9(A_1849, B_1850, C_1851), A_1849) | ~v6_waybel_0(k4_waybel_9(A_1849, B_1850, C_1851), A_1849) | ~m1_subset_1(C_1851, u1_struct_0(B_1850)) | ~l1_waybel_0(B_1850, A_1849) | v2_struct_0(B_1850) | ~l1_struct_0(A_1849) | v2_struct_0(A_1849))), inference(cnfTransformation, [status(thm)], [f_146])).
% 10.69/4.11  tff(c_5948, plain, (![B_2183, A_2184, C_2185]: (k1_toler_1(u1_orders_2(B_2183), u1_struct_0(k4_waybel_9(A_2184, B_2183, C_2185)))=u1_orders_2(k4_waybel_9(A_2184, B_2183, C_2185)) | ~m1_subset_1(k1_toler_1(u1_orders_2(B_2183), u1_struct_0(k4_waybel_9(A_2184, B_2183, C_2185))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_2184, B_2183, C_2185)), u1_struct_0(k4_waybel_9(A_2184, B_2183, C_2185))))) | ~m1_subset_1(u1_orders_2(k4_waybel_9(A_2184, B_2183, C_2185)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_2184, B_2183, C_2185)), u1_struct_0(k4_waybel_9(A_2184, B_2183, C_2185))))) | ~l1_waybel_0(k4_waybel_9(A_2184, B_2183, C_2185), A_2184) | ~v6_waybel_0(k4_waybel_9(A_2184, B_2183, C_2185), A_2184) | ~m1_subset_1(C_2185, u1_struct_0(B_2183)) | ~l1_waybel_0(B_2183, A_2184) | v2_struct_0(B_2183) | ~l1_struct_0(A_2184) | v2_struct_0(A_2184))), inference(resolution, [status(thm)], [c_5207, c_10])).
% 10.69/4.11  tff(c_6498, plain, (![B_2340, A_2341, C_2342]: (k1_toler_1(u1_orders_2(B_2340), u1_struct_0(k4_waybel_9(A_2341, B_2340, C_2342)))=u1_orders_2(k4_waybel_9(A_2341, B_2340, C_2342)) | ~m1_subset_1(u1_orders_2(k4_waybel_9(A_2341, B_2340, C_2342)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k4_waybel_9(A_2341, B_2340, C_2342)), u1_struct_0(k4_waybel_9(A_2341, B_2340, C_2342))))) | ~l1_waybel_0(k4_waybel_9(A_2341, B_2340, C_2342), A_2341) | ~v6_waybel_0(k4_waybel_9(A_2341, B_2340, C_2342), A_2341) | ~m1_subset_1(C_2342, u1_struct_0(B_2340)) | ~l1_waybel_0(B_2340, A_2341) | v2_struct_0(B_2340) | ~l1_struct_0(A_2341) | v2_struct_0(A_2341) | ~v1_relat_1(u1_orders_2(B_2340)))), inference(resolution, [status(thm)], [c_24, c_5948])).
% 10.69/4.11  tff(c_6547, plain, (![B_2373, A_2374, C_2375]: (k1_toler_1(u1_orders_2(B_2373), u1_struct_0(k4_waybel_9(A_2374, B_2373, C_2375)))=u1_orders_2(k4_waybel_9(A_2374, B_2373, C_2375)) | ~l1_waybel_0(k4_waybel_9(A_2374, B_2373, C_2375), A_2374) | ~v6_waybel_0(k4_waybel_9(A_2374, B_2373, C_2375), A_2374) | ~m1_subset_1(C_2375, u1_struct_0(B_2373)) | ~l1_waybel_0(B_2373, A_2374) | v2_struct_0(B_2373) | ~l1_struct_0(A_2374) | v2_struct_0(A_2374) | ~v1_relat_1(u1_orders_2(B_2373)) | ~l1_orders_2(k4_waybel_9(A_2374, B_2373, C_2375)))), inference(resolution, [status(thm)], [c_12, c_6498])).
% 10.69/4.11  tff(c_6549, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_5368, c_6547])).
% 10.69/4.11  tff(c_6554, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_6549])).
% 10.69/4.11  tff(c_6555, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_6554])).
% 10.69/4.11  tff(c_6557, plain, (~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_6555])).
% 10.69/4.11  tff(c_6576, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4904, c_6557])).
% 10.69/4.11  tff(c_6579, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_6576])).
% 10.69/4.11  tff(c_6581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6579])).
% 10.69/4.11  tff(c_6583, plain, (l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6555])).
% 10.69/4.11  tff(c_4775, plain, (![A_1677]: (m1_subset_1(u1_orders_2(A_1677), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1677), u1_struct_0(A_1677)))) | ~l1_orders_2(A_1677))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.69/4.11  tff(c_4779, plain, (![A_1677]: (v1_relat_1(u1_orders_2(A_1677)) | ~l1_orders_2(A_1677))), inference(resolution, [status(thm)], [c_4775, c_6])).
% 10.69/4.11  tff(c_6582, plain, (~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5') | k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6555])).
% 10.69/4.11  tff(c_6584, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitLeft, [status(thm)], [c_6582])).
% 10.69/4.11  tff(c_6587, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4899, c_6584])).
% 10.69/4.11  tff(c_6590, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_6587])).
% 10.69/4.11  tff(c_6592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_6590])).
% 10.69/4.11  tff(c_6593, plain, (~v1_relat_1(u1_orders_2('#skF_6')) | k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6582])).
% 10.69/4.11  tff(c_6633, plain, (~v1_relat_1(u1_orders_2('#skF_6'))), inference(splitLeft, [status(thm)], [c_6593])).
% 10.69/4.11  tff(c_6636, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_4779, c_6633])).
% 10.69/4.11  tff(c_6640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_6636])).
% 10.69/4.11  tff(c_6642, plain, (v1_relat_1(u1_orders_2('#skF_6'))), inference(splitRight, [status(thm)], [c_6593])).
% 10.69/4.11  tff(c_6641, plain, (k1_toler_1(u1_orders_2('#skF_6'), u1_struct_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')))=u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6593])).
% 10.69/4.11  tff(c_4780, plain, (![A_1678]: (v1_relat_1(u1_orders_2(A_1678)) | ~l1_orders_2(A_1678))), inference(resolution, [status(thm)], [c_4775, c_6])).
% 10.69/4.11  tff(c_4791, plain, (![A_1682, B_1683]: (k2_wellord1(u1_orders_2(A_1682), B_1683)=k1_toler_1(u1_orders_2(A_1682), B_1683) | ~l1_orders_2(A_1682))), inference(resolution, [status(thm)], [c_4780, c_26])).
% 10.69/4.11  tff(c_4762, plain, (![A_1673, B_1674]: (k3_xboole_0(A_1673, k2_zfmisc_1(B_1674, B_1674))=k2_wellord1(A_1673, B_1674) | ~v1_relat_1(A_1673))), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.69/4.11  tff(c_4768, plain, (![A_1673, B_1674]: (r1_tarski(k2_wellord1(A_1673, B_1674), A_1673) | ~v1_relat_1(A_1673))), inference(superposition, [status(thm), theory('equality')], [c_4762, c_2])).
% 10.69/4.11  tff(c_4797, plain, (![A_1682, B_1683]: (r1_tarski(k1_toler_1(u1_orders_2(A_1682), B_1683), u1_orders_2(A_1682)) | ~v1_relat_1(u1_orders_2(A_1682)) | ~l1_orders_2(A_1682))), inference(superposition, [status(thm), theory('equality')], [c_4791, c_4768])).
% 10.69/4.11  tff(c_6885, plain, (r1_tarski(u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')), u1_orders_2('#skF_6')) | ~v1_relat_1(u1_orders_2('#skF_6')) | ~l1_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6641, c_4797])).
% 10.69/4.11  tff(c_7017, plain, (r1_tarski(u1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')), u1_orders_2('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_6642, c_6885])).
% 10.69/4.11  tff(c_4921, plain, (![A_1739, B_1740, C_1741]: (r1_tarski(u1_struct_0(k4_waybel_9(A_1739, B_1740, C_1741)), u1_struct_0(B_1740)) | ~m1_subset_1(C_1741, u1_struct_0(B_1740)) | ~l1_waybel_0(B_1740, A_1739) | v2_struct_0(B_1740) | ~l1_struct_0(A_1739) | v2_struct_0(A_1739))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.69/4.11  tff(c_4925, plain, (![A_1739, B_1740, C_1741]: (m1_yellow_0(k4_waybel_9(A_1739, B_1740, C_1741), B_1740) | ~r1_tarski(u1_orders_2(k4_waybel_9(A_1739, B_1740, C_1741)), u1_orders_2(B_1740)) | ~l1_orders_2(k4_waybel_9(A_1739, B_1740, C_1741)) | ~l1_orders_2(B_1740) | ~m1_subset_1(C_1741, u1_struct_0(B_1740)) | ~l1_waybel_0(B_1740, A_1739) | v2_struct_0(B_1740) | ~l1_struct_0(A_1739) | v2_struct_0(A_1739))), inference(resolution, [status(thm)], [c_4921, c_14])).
% 10.69/4.11  tff(c_7048, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | ~l1_orders_2(k4_waybel_9('#skF_5', '#skF_6', '#skF_7')) | ~l1_orders_2('#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_7017, c_4925])).
% 10.69/4.11  tff(c_7051, plain, (m1_yellow_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_6') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_94, c_6583, c_7048])).
% 10.69/4.11  tff(c_7053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_82, c_5376, c_7051])).
% 10.69/4.11  tff(c_7054, plain, (~l1_waybel_0(k4_waybel_9('#skF_5', '#skF_6', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_5367])).
% 10.69/4.11  tff(c_7058, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4899, c_7054])).
% 10.69/4.11  tff(c_7061, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_7058])).
% 10.69/4.11  tff(c_7063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_7061])).
% 10.69/4.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.69/4.11  
% 10.69/4.11  Inference rules
% 10.69/4.11  ----------------------
% 10.69/4.11  #Ref     : 0
% 10.69/4.11  #Sup     : 1748
% 10.69/4.11  #Fact    : 0
% 10.69/4.11  #Define  : 0
% 10.69/4.11  #Split   : 22
% 10.69/4.11  #Chain   : 0
% 10.69/4.11  #Close   : 0
% 10.69/4.11  
% 10.69/4.11  Ordering : KBO
% 10.69/4.11  
% 10.69/4.11  Simplification rules
% 10.69/4.11  ----------------------
% 10.69/4.11  #Subsume      : 623
% 10.69/4.11  #Demod        : 728
% 10.69/4.11  #Tautology    : 146
% 10.69/4.11  #SimpNegUnit  : 130
% 10.69/4.11  #BackRed      : 0
% 10.69/4.11  
% 10.69/4.11  #Partial instantiations: 0
% 10.69/4.11  #Strategies tried      : 1
% 10.69/4.11  
% 10.69/4.11  Timing (in seconds)
% 10.69/4.11  ----------------------
% 10.69/4.11  Preprocessing        : 0.42
% 10.69/4.11  Parsing              : 0.20
% 10.69/4.11  CNF conversion       : 0.04
% 10.69/4.11  Main loop            : 2.88
% 10.69/4.11  Inferencing          : 1.15
% 10.69/4.11  Reduction            : 0.69
% 10.69/4.11  Demodulation         : 0.45
% 10.69/4.11  BG Simplification    : 0.12
% 10.69/4.11  Subsumption          : 0.77
% 10.69/4.11  Abstraction          : 0.13
% 10.69/4.11  MUC search           : 0.00
% 10.69/4.11  Cooper               : 0.00
% 10.69/4.11  Total                : 3.37
% 10.69/4.11  Index Insertion      : 0.00
% 10.69/4.11  Index Deletion       : 0.00
% 10.69/4.11  Index Matching       : 0.00
% 10.69/4.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
