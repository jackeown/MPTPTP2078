%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:20 EST 2020

% Result     : Theorem 11.82s
% Output     : CNFRefutation 12.13s
% Verified   : 
% Statistics : Number of formulae       :  298 (3134 expanded)
%              Number of leaves         :   47 (1055 expanded)
%              Depth                    :   24
%              Number of atoms          :  884 (12629 expanded)
%              Number of equality atoms :  127 (1099 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(l3_lattices,type,(
    l3_lattices: $i > $o )).

tff(k3_lattices,type,(
    k3_lattices: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k2_lattices,type,(
    k2_lattices: ( $i * $i * $i ) > $i )).

tff(l2_lattices,type,(
    l2_lattices: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(r3_lattices,type,(
    r3_lattices: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_lattices,type,(
    k4_lattices: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_lattices,type,(
    k1_lattices: ( $i * $i * $i ) > $i )).

tff(l1_lattices,type,(
    l1_lattices: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_lattices,type,(
    r1_lattices: ( $i * $i * $i ) > $o )).

tff(v17_lattices,type,(
    v17_lattices: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v4_lattices,type,(
    v4_lattices: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v6_lattices,type,(
    v6_lattices: $i > $o )).

tff(v9_lattices,type,(
    v9_lattices: $i > $o )).

tff(v5_lattices,type,(
    v5_lattices: $i > $o )).

tff(v10_lattices,type,(
    v10_lattices: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(v8_lattices,type,(
    v8_lattices: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k7_lattices,type,(
    k7_lattices: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v7_lattices,type,(
    v7_lattices: $i > $o )).

tff(f_279,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v10_lattices(A)
          & v17_lattices(A)
          & l3_lattices(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_lattices(A,B,C)
                 => r3_lattices(A,k7_lattices(A,C),k7_lattices(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_lattices)).

tff(f_47,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( ( ~ v2_struct_0(A)
          & v10_lattices(A) )
       => ( ~ v2_struct_0(A)
          & v4_lattices(A)
          & v5_lattices(A)
          & v6_lattices(A)
          & v7_lattices(A)
          & v8_lattices(A)
          & v9_lattices(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

tff(f_118,axiom,(
    ! [A] :
      ( l3_lattices(A)
     => ( l1_lattices(A)
        & l2_lattices(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

tff(f_62,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k1_lattices(A,B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v8_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k1_lattices(A,k2_lattices(A,B,C),C) = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A) )
     => ( v9_lattices(A)
      <=> ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => k2_lattices(A,B,k1_lattices(A,B,C)) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

tff(f_199,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r1_lattices(A,B,C)
              <=> k2_lattices(A,B,C) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

tff(f_180,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_lattices(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

tff(f_163,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_lattices(A,B,C)
      <=> r1_lattices(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

tff(f_131,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k3_lattices(A,B,C) = k1_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

tff(f_242,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_lattices(A)
        & v8_lattices(A)
        & v9_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattices(A,B,C)
                   => r1_lattices(A,k2_lattices(A,B,D),k2_lattices(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_lattices)).

tff(f_144,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v6_lattices(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k4_lattices(A,B,C) = k2_lattices(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_lattices(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k2_lattices(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

tff(f_218,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v4_lattices(A)
        & l2_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_lattices(A,B,C)
                  & r1_lattices(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l3_lattices(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k7_lattices(A,B),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

tff(f_259,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v10_lattices(A)
        & v17_lattices(A)
        & l3_lattices(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k7_lattices(A,k4_lattices(A,B,C)) = k3_lattices(A,k7_lattices(A,B),k7_lattices(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_72,plain,(
    l3_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_76,plain,(
    v10_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_2,plain,(
    ! [A_1] :
      ( v9_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v8_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_84,plain,(
    ! [A_90] :
      ( l2_lattices(A_90)
      | ~ l3_lattices(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_88,plain,(
    l2_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_84])).

tff(c_104,plain,(
    ! [A_111,B_112,C_113] :
      ( r1_lattices(A_111,B_112,C_113)
      | k1_lattices(A_111,B_112,C_113) != C_113
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l2_lattices(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_118,plain,(
    ! [B_112] :
      ( r1_lattices('#skF_5',B_112,'#skF_7')
      | k1_lattices('#skF_5',B_112,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_104])).

tff(c_129,plain,(
    ! [B_112] :
      ( r1_lattices('#skF_5',B_112,'#skF_7')
      | k1_lattices('#skF_5',B_112,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_118])).

tff(c_135,plain,(
    ! [B_114] :
      ( r1_lattices('#skF_5',B_114,'#skF_7')
      | k1_lattices('#skF_5',B_114,'#skF_7') != '#skF_7'
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_129])).

tff(c_191,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_7')
    | k1_lattices('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(resolution,[status(thm)],[c_70,c_135])).

tff(c_3865,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_7') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_3970,plain,(
    ! [A_251,B_252,C_253] :
      ( k1_lattices(A_251,k2_lattices(A_251,B_252,C_253),C_253) = C_253
      | ~ m1_subset_1(C_253,u1_struct_0(A_251))
      | ~ m1_subset_1(B_252,u1_struct_0(A_251))
      | ~ v8_lattices(A_251)
      | ~ l3_lattices(A_251)
      | v2_struct_0(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3984,plain,(
    ! [B_252] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_252,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_3970])).

tff(c_3995,plain,(
    ! [B_252] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_252,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3984])).

tff(c_3996,plain,(
    ! [B_252] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_252,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_252,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3995])).

tff(c_4037,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3996])).

tff(c_4041,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_4037])).

tff(c_4044,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_4041])).

tff(c_4046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4044])).

tff(c_4048,plain,(
    v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_3996])).

tff(c_32,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_4'(A_20),u1_struct_0(A_20))
      | v9_lattices(A_20)
      | ~ l3_lattices(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4049,plain,(
    ! [B_257] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_257,'#skF_7'),'#skF_7') = '#skF_7'
      | ~ m1_subset_1(B_257,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_3996])).

tff(c_4065,plain,
    ( k1_lattices('#skF_5',k2_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7'),'#skF_7') = '#skF_7'
    | v9_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_4049])).

tff(c_4094,plain,
    ( k1_lattices('#skF_5',k2_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7'),'#skF_7') = '#skF_7'
    | v9_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4065])).

tff(c_4095,plain,
    ( k1_lattices('#skF_5',k2_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7'),'#skF_7') = '#skF_7'
    | v9_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4094])).

tff(c_4145,plain,(
    v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4095])).

tff(c_4798,plain,(
    ! [A_280,B_281,C_282] :
      ( r1_lattices(A_280,B_281,C_282)
      | k2_lattices(A_280,B_281,C_282) != B_281
      | ~ m1_subset_1(C_282,u1_struct_0(A_280))
      | ~ m1_subset_1(B_281,u1_struct_0(A_280))
      | ~ l3_lattices(A_280)
      | ~ v9_lattices(A_280)
      | ~ v8_lattices(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_4812,plain,(
    ! [B_281] :
      ( r1_lattices('#skF_5',B_281,'#skF_7')
      | k2_lattices('#skF_5',B_281,'#skF_7') != B_281
      | ~ m1_subset_1(B_281,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_4798])).

tff(c_4823,plain,(
    ! [B_281] :
      ( r1_lattices('#skF_5',B_281,'#skF_7')
      | k2_lattices('#skF_5',B_281,'#skF_7') != B_281
      | ~ m1_subset_1(B_281,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4048,c_4145,c_72,c_4812])).

tff(c_4829,plain,(
    ! [B_283] :
      ( r1_lattices('#skF_5',B_283,'#skF_7')
      | k2_lattices('#skF_5',B_283,'#skF_7') != B_283
      | ~ m1_subset_1(B_283,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4823])).

tff(c_4887,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_7')
    | k2_lattices('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_4829])).

tff(c_4888,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4887])).

tff(c_8,plain,(
    ! [A_1] :
      ( v6_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4288,plain,(
    ! [A_263,B_264,C_265] :
      ( r3_lattices(A_263,B_264,B_264)
      | ~ m1_subset_1(C_265,u1_struct_0(A_263))
      | ~ m1_subset_1(B_264,u1_struct_0(A_263))
      | ~ l3_lattices(A_263)
      | ~ v9_lattices(A_263)
      | ~ v8_lattices(A_263)
      | ~ v6_lattices(A_263)
      | v2_struct_0(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_4302,plain,(
    ! [B_264] :
      ( r3_lattices('#skF_5',B_264,B_264)
      | ~ m1_subset_1(B_264,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_4288])).

tff(c_4313,plain,(
    ! [B_264] :
      ( r3_lattices('#skF_5',B_264,B_264)
      | ~ m1_subset_1(B_264,u1_struct_0('#skF_5'))
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4048,c_4145,c_72,c_4302])).

tff(c_4314,plain,(
    ! [B_264] :
      ( r3_lattices('#skF_5',B_264,B_264)
      | ~ m1_subset_1(B_264,u1_struct_0('#skF_5'))
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4313])).

tff(c_4319,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4314])).

tff(c_4322,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_4319])).

tff(c_4325,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_4322])).

tff(c_4327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4325])).

tff(c_4329,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4314])).

tff(c_66,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_4957,plain,(
    ! [A_286,B_287,C_288] :
      ( r1_lattices(A_286,B_287,C_288)
      | ~ r3_lattices(A_286,B_287,C_288)
      | ~ m1_subset_1(C_288,u1_struct_0(A_286))
      | ~ m1_subset_1(B_287,u1_struct_0(A_286))
      | ~ l3_lattices(A_286)
      | ~ v9_lattices(A_286)
      | ~ v8_lattices(A_286)
      | ~ v6_lattices(A_286)
      | v2_struct_0(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_4965,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_4957])).

tff(c_4980,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4329,c_4048,c_4145,c_72,c_70,c_68,c_4965])).

tff(c_4981,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4980])).

tff(c_56,plain,(
    ! [A_49,B_53,C_55] :
      ( k2_lattices(A_49,B_53,C_55) = B_53
      | ~ r1_lattices(A_49,B_53,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(A_49))
      | ~ m1_subset_1(B_53,u1_struct_0(A_49))
      | ~ l3_lattices(A_49)
      | ~ v9_lattices(A_49)
      | ~ v8_lattices(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_4983,plain,
    ( k2_lattices('#skF_5','#skF_6','#skF_7') = '#skF_6'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4981,c_56])).

tff(c_4990,plain,
    ( k2_lattices('#skF_5','#skF_6','#skF_7') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4048,c_4145,c_72,c_70,c_68,c_4983])).

tff(c_4992,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4888,c_4990])).

tff(c_4993,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_4887])).

tff(c_18,plain,(
    ! [A_2,B_6,C_8] :
      ( k1_lattices(A_2,B_6,C_8) = C_8
      | ~ r1_lattices(A_2,B_6,C_8)
      | ~ m1_subset_1(C_8,u1_struct_0(A_2))
      | ~ m1_subset_1(B_6,u1_struct_0(A_2))
      | ~ l2_lattices(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5000,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4993,c_18])).

tff(c_5011,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_70,c_68,c_5000])).

tff(c_5013,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3865,c_5011])).

tff(c_5015,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_4095])).

tff(c_5018,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_5015])).

tff(c_5021,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_5018])).

tff(c_5023,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5021])).

tff(c_5024,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_6,plain,(
    ! [A_1] :
      ( v7_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_1'(A_9),u1_struct_0(A_9))
      | v8_lattices(A_9)
      | ~ l3_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_1] :
      ( v4_lattices(A_1)
      | ~ v10_lattices(A_1)
      | v2_struct_0(A_1)
      | ~ l3_lattices(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6615,plain,(
    ! [A_343,B_344,C_345] :
      ( k3_lattices(A_343,B_344,C_345) = k1_lattices(A_343,B_344,C_345)
      | ~ m1_subset_1(C_345,u1_struct_0(A_343))
      | ~ m1_subset_1(B_344,u1_struct_0(A_343))
      | ~ l2_lattices(A_343)
      | ~ v4_lattices(A_343)
      | v2_struct_0(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6629,plain,(
    ! [B_344] :
      ( k3_lattices('#skF_5',B_344,'#skF_7') = k1_lattices('#skF_5',B_344,'#skF_7')
      | ~ m1_subset_1(B_344,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | ~ v4_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_6615])).

tff(c_6640,plain,(
    ! [B_344] :
      ( k3_lattices('#skF_5',B_344,'#skF_7') = k1_lattices('#skF_5',B_344,'#skF_7')
      | ~ m1_subset_1(B_344,u1_struct_0('#skF_5'))
      | ~ v4_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_6629])).

tff(c_6641,plain,(
    ! [B_344] :
      ( k3_lattices('#skF_5',B_344,'#skF_7') = k1_lattices('#skF_5',B_344,'#skF_7')
      | ~ m1_subset_1(B_344,u1_struct_0('#skF_5'))
      | ~ v4_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6640])).

tff(c_6648,plain,(
    ~ v4_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6641])).

tff(c_6651,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_6648])).

tff(c_6654,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_6651])).

tff(c_6656,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6654])).

tff(c_6659,plain,(
    ! [B_346] :
      ( k3_lattices('#skF_5',B_346,'#skF_7') = k1_lattices('#skF_5',B_346,'#skF_7')
      | ~ m1_subset_1(B_346,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_6641])).

tff(c_6671,plain,
    ( k3_lattices('#skF_5','#skF_1'('#skF_5'),'#skF_7') = k1_lattices('#skF_5','#skF_1'('#skF_5'),'#skF_7')
    | v8_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_6659])).

tff(c_6700,plain,
    ( k3_lattices('#skF_5','#skF_1'('#skF_5'),'#skF_7') = k1_lattices('#skF_5','#skF_1'('#skF_5'),'#skF_7')
    | v8_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6671])).

tff(c_6701,plain,
    ( k3_lattices('#skF_5','#skF_1'('#skF_5'),'#skF_7') = k1_lattices('#skF_5','#skF_1'('#skF_5'),'#skF_7')
    | v8_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6700])).

tff(c_6759,plain,(
    v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6701])).

tff(c_6675,plain,
    ( k3_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7') = k1_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7')
    | v9_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_6659])).

tff(c_6704,plain,
    ( k3_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7') = k1_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7')
    | v9_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6675])).

tff(c_6705,plain,
    ( k3_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7') = k1_lattices('#skF_5','#skF_4'('#skF_5'),'#skF_7')
    | v9_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6704])).

tff(c_6757,plain,(
    v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6705])).

tff(c_5025,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_6580,plain,(
    ! [A_340,B_341,C_342] :
      ( k2_lattices(A_340,B_341,k1_lattices(A_340,B_341,C_342)) = B_341
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ m1_subset_1(B_341,u1_struct_0(A_340))
      | ~ v9_lattices(A_340)
      | ~ l3_lattices(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_6594,plain,(
    ! [B_341] :
      ( k2_lattices('#skF_5',B_341,k1_lattices('#skF_5',B_341,'#skF_7')) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_6580])).

tff(c_6605,plain,(
    ! [B_341] :
      ( k2_lattices('#skF_5',B_341,k1_lattices('#skF_5',B_341,'#skF_7')) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6594])).

tff(c_6606,plain,(
    ! [B_341] :
      ( k2_lattices('#skF_5',B_341,k1_lattices('#skF_5',B_341,'#skF_7')) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6605])).

tff(c_7164,plain,(
    ! [B_361] :
      ( k2_lattices('#skF_5',B_361,k1_lattices('#skF_5',B_361,'#skF_7')) = B_361
      | ~ m1_subset_1(B_361,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_6606])).

tff(c_7186,plain,(
    k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_7')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_7164])).

tff(c_7214,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5025,c_7186])).

tff(c_8302,plain,(
    ! [A_409,B_410,D_411,C_412] :
      ( r1_lattices(A_409,k2_lattices(A_409,B_410,D_411),k2_lattices(A_409,C_412,D_411))
      | ~ r1_lattices(A_409,B_410,C_412)
      | ~ m1_subset_1(D_411,u1_struct_0(A_409))
      | ~ m1_subset_1(C_412,u1_struct_0(A_409))
      | ~ m1_subset_1(B_410,u1_struct_0(A_409))
      | ~ l3_lattices(A_409)
      | ~ v9_lattices(A_409)
      | ~ v8_lattices(A_409)
      | ~ v7_lattices(A_409)
      | v2_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_8323,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_7'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v7_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7214,c_8302])).

tff(c_8361,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_7'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5'))
      | ~ v7_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6759,c_6757,c_72,c_70,c_68,c_8323])).

tff(c_8362,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_7'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5'))
      | ~ v7_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8361])).

tff(c_8384,plain,(
    ~ v7_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8362])).

tff(c_8387,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_8384])).

tff(c_8390,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_8387])).

tff(c_8392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8390])).

tff(c_8394,plain,(
    v7_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_8362])).

tff(c_120,plain,(
    ! [B_112] :
      ( r1_lattices('#skF_5',B_112,'#skF_6')
      | k1_lattices('#skF_5',B_112,'#skF_6') != '#skF_6'
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5'))
      | ~ l2_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_104])).

tff(c_133,plain,(
    ! [B_112] :
      ( r1_lattices('#skF_5',B_112,'#skF_6')
      | k1_lattices('#skF_5',B_112,'#skF_6') != '#skF_6'
      | ~ m1_subset_1(B_112,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_120])).

tff(c_5026,plain,(
    ! [B_289] :
      ( r1_lattices('#skF_5',B_289,'#skF_6')
      | k1_lattices('#skF_5',B_289,'#skF_6') != '#skF_6'
      | ~ m1_subset_1(B_289,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_133])).

tff(c_5082,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | k1_lattices('#skF_5','#skF_6','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_5026])).

tff(c_5137,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_6') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5082])).

tff(c_24,plain,(
    ! [A_9] :
      ( m1_subset_1('#skF_2'(A_9),u1_struct_0(A_9))
      | v8_lattices(A_9)
      | ~ l3_lattices(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5176,plain,(
    ! [A_296,B_297,C_298] :
      ( k2_lattices(A_296,B_297,k1_lattices(A_296,B_297,C_298)) = B_297
      | ~ m1_subset_1(C_298,u1_struct_0(A_296))
      | ~ m1_subset_1(B_297,u1_struct_0(A_296))
      | ~ v9_lattices(A_296)
      | ~ l3_lattices(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5190,plain,(
    ! [B_297] :
      ( k2_lattices('#skF_5',B_297,k1_lattices('#skF_5',B_297,'#skF_7')) = B_297
      | ~ m1_subset_1(B_297,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_5176])).

tff(c_5201,plain,(
    ! [B_297] :
      ( k2_lattices('#skF_5',B_297,k1_lattices('#skF_5',B_297,'#skF_7')) = B_297
      | ~ m1_subset_1(B_297,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5190])).

tff(c_5202,plain,(
    ! [B_297] :
      ( k2_lattices('#skF_5',B_297,k1_lattices('#skF_5',B_297,'#skF_7')) = B_297
      | ~ m1_subset_1(B_297,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5201])).

tff(c_5208,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5202])).

tff(c_5211,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_5208])).

tff(c_5214,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_5211])).

tff(c_5216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5214])).

tff(c_5219,plain,(
    ! [B_299] :
      ( k2_lattices('#skF_5',B_299,k1_lattices('#skF_5',B_299,'#skF_7')) = B_299
      | ~ m1_subset_1(B_299,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_5202])).

tff(c_5234,plain,
    ( k2_lattices('#skF_5','#skF_2'('#skF_5'),k1_lattices('#skF_5','#skF_2'('#skF_5'),'#skF_7')) = '#skF_2'('#skF_5')
    | v8_lattices('#skF_5')
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_5219])).

tff(c_5260,plain,
    ( k2_lattices('#skF_5','#skF_2'('#skF_5'),k1_lattices('#skF_5','#skF_2'('#skF_5'),'#skF_7')) = '#skF_2'('#skF_5')
    | v8_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5234])).

tff(c_5261,plain,
    ( k2_lattices('#skF_5','#skF_2'('#skF_5'),k1_lattices('#skF_5','#skF_2'('#skF_5'),'#skF_7')) = '#skF_2'('#skF_5')
    | v8_lattices('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5260])).

tff(c_5321,plain,(
    v8_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5261])).

tff(c_5218,plain,(
    v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5202])).

tff(c_5934,plain,(
    ! [A_322,B_323,C_324] :
      ( r1_lattices(A_322,B_323,C_324)
      | k2_lattices(A_322,B_323,C_324) != B_323
      | ~ m1_subset_1(C_324,u1_struct_0(A_322))
      | ~ m1_subset_1(B_323,u1_struct_0(A_322))
      | ~ l3_lattices(A_322)
      | ~ v9_lattices(A_322)
      | ~ v8_lattices(A_322)
      | v2_struct_0(A_322) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_5950,plain,(
    ! [B_323] :
      ( r1_lattices('#skF_5',B_323,'#skF_6')
      | k2_lattices('#skF_5',B_323,'#skF_6') != B_323
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_5934])).

tff(c_5963,plain,(
    ! [B_323] :
      ( r1_lattices('#skF_5',B_323,'#skF_6')
      | k2_lattices('#skF_5',B_323,'#skF_6') != B_323
      | ~ m1_subset_1(B_323,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5321,c_5218,c_72,c_5950])).

tff(c_6026,plain,(
    ! [B_326] :
      ( r1_lattices('#skF_5',B_326,'#skF_6')
      | k2_lattices('#skF_5',B_326,'#skF_6') != B_326
      | ~ m1_subset_1(B_326,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5963])).

tff(c_6084,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | k2_lattices('#skF_5','#skF_6','#skF_6') != '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_6026])).

tff(c_6085,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_6') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6084])).

tff(c_79,plain,(
    ! [A_89] :
      ( l1_lattices(A_89)
      | ~ l3_lattices(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_83,plain,(
    l1_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_79])).

tff(c_5290,plain,(
    ! [A_300,B_301,C_302] :
      ( k4_lattices(A_300,B_301,C_302) = k2_lattices(A_300,B_301,C_302)
      | ~ m1_subset_1(C_302,u1_struct_0(A_300))
      | ~ m1_subset_1(B_301,u1_struct_0(A_300))
      | ~ l1_lattices(A_300)
      | ~ v6_lattices(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5306,plain,(
    ! [B_301] :
      ( k4_lattices('#skF_5',B_301,'#skF_6') = k2_lattices('#skF_5',B_301,'#skF_6')
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_5'))
      | ~ l1_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_5290])).

tff(c_5319,plain,(
    ! [B_301] :
      ( k4_lattices('#skF_5',B_301,'#skF_6') = k2_lattices('#skF_5',B_301,'#skF_6')
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_5'))
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_5306])).

tff(c_5320,plain,(
    ! [B_301] :
      ( k4_lattices('#skF_5',B_301,'#skF_6') = k2_lattices('#skF_5',B_301,'#skF_6')
      | ~ m1_subset_1(B_301,u1_struct_0('#skF_5'))
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5319])).

tff(c_5384,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_5320])).

tff(c_5387,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_5384])).

tff(c_5390,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_5387])).

tff(c_5392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5390])).

tff(c_5394,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5320])).

tff(c_5104,plain,(
    ! [A_290,B_291,C_292] :
      ( r3_lattices(A_290,B_291,B_291)
      | ~ m1_subset_1(C_292,u1_struct_0(A_290))
      | ~ m1_subset_1(B_291,u1_struct_0(A_290))
      | ~ l3_lattices(A_290)
      | ~ v9_lattices(A_290)
      | ~ v8_lattices(A_290)
      | ~ v6_lattices(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_5120,plain,(
    ! [B_291] :
      ( r3_lattices('#skF_5',B_291,B_291)
      | ~ m1_subset_1(B_291,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_5104])).

tff(c_5133,plain,(
    ! [B_291] :
      ( r3_lattices('#skF_5',B_291,B_291)
      | ~ m1_subset_1(B_291,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_5120])).

tff(c_5134,plain,(
    ! [B_291] :
      ( r3_lattices('#skF_5',B_291,B_291)
      | ~ m1_subset_1(B_291,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5133])).

tff(c_5493,plain,(
    ! [B_308] :
      ( r3_lattices('#skF_5',B_308,B_308)
      | ~ m1_subset_1(B_308,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5394,c_5321,c_5218,c_5134])).

tff(c_5541,plain,(
    r3_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_5493])).

tff(c_6497,plain,(
    ! [A_337,B_338,C_339] :
      ( r1_lattices(A_337,B_338,C_339)
      | ~ r3_lattices(A_337,B_338,C_339)
      | ~ m1_subset_1(C_339,u1_struct_0(A_337))
      | ~ m1_subset_1(B_338,u1_struct_0(A_337))
      | ~ l3_lattices(A_337)
      | ~ v9_lattices(A_337)
      | ~ v8_lattices(A_337)
      | ~ v6_lattices(A_337)
      | v2_struct_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_6501,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_5541,c_6497])).

tff(c_6512,plain,
    ( r1_lattices('#skF_5','#skF_6','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5394,c_5321,c_5218,c_72,c_70,c_6501])).

tff(c_6513,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6512])).

tff(c_6523,plain,
    ( k2_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6513,c_56])).

tff(c_6530,plain,
    ( k2_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5321,c_5218,c_72,c_70,c_6523])).

tff(c_6532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6085,c_6530])).

tff(c_6533,plain,(
    r1_lattices('#skF_5','#skF_6','#skF_6') ),
    inference(splitRight,[status(thm)],[c_6084])).

tff(c_6540,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6533,c_18])).

tff(c_6552,plain,
    ( k1_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_70,c_6540])).

tff(c_6554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5137,c_6552])).

tff(c_6556,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_5261])).

tff(c_6559,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_6556])).

tff(c_6562,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_6559])).

tff(c_6564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6562])).

tff(c_6566,plain,(
    k1_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5082])).

tff(c_6596,plain,(
    ! [B_341] :
      ( k2_lattices('#skF_5',B_341,k1_lattices('#skF_5',B_341,'#skF_6')) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_6580])).

tff(c_6609,plain,(
    ! [B_341] :
      ( k2_lattices('#skF_5',B_341,k1_lattices('#skF_5',B_341,'#skF_6')) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6596])).

tff(c_6610,plain,(
    ! [B_341] :
      ( k2_lattices('#skF_5',B_341,k1_lattices('#skF_5',B_341,'#skF_6')) = B_341
      | ~ m1_subset_1(B_341,u1_struct_0('#skF_5'))
      | ~ v9_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6609])).

tff(c_6763,plain,(
    ! [B_350] :
      ( k2_lattices('#skF_5',B_350,k1_lattices('#skF_5',B_350,'#skF_6')) = B_350
      | ~ m1_subset_1(B_350,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6757,c_6610])).

tff(c_6785,plain,(
    k2_lattices('#skF_5','#skF_6',k1_lattices('#skF_5','#skF_6','#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_6763])).

tff(c_6812,plain,(
    k2_lattices('#skF_5','#skF_6','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6566,c_6785])).

tff(c_8341,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_6'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v9_lattices('#skF_5')
      | ~ v8_lattices('#skF_5')
      | ~ v7_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6812,c_8302])).

tff(c_8379,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_6'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5'))
      | ~ v7_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6759,c_6757,c_72,c_70,c_70,c_8341])).

tff(c_8380,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_6'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5'))
      | ~ v7_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8379])).

tff(c_8451,plain,(
    ! [C_412] :
      ( r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5',C_412,'#skF_6'))
      | ~ r1_lattices('#skF_5','#skF_6',C_412)
      | ~ m1_subset_1(C_412,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8394,c_8380])).

tff(c_6658,plain,(
    v4_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6641])).

tff(c_36,plain,(
    ! [A_31,B_32,C_33] :
      ( m1_subset_1(k2_lattices(A_31,B_32,C_33),u1_struct_0(A_31))
      | ~ m1_subset_1(C_33,u1_struct_0(A_31))
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_lattices(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6722,plain,(
    ! [A_347,B_348,C_349] :
      ( k1_lattices(A_347,k2_lattices(A_347,B_348,C_349),C_349) = C_349
      | ~ m1_subset_1(C_349,u1_struct_0(A_347))
      | ~ m1_subset_1(B_348,u1_struct_0(A_347))
      | ~ v8_lattices(A_347)
      | ~ l3_lattices(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6738,plain,(
    ! [B_348] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_348,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_348,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_6722])).

tff(c_6751,plain,(
    ! [B_348] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_348,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_348,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6738])).

tff(c_6752,plain,(
    ! [B_348] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_348,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_348,u1_struct_0('#skF_5'))
      | ~ v8_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6751])).

tff(c_7032,plain,(
    ! [B_359] :
      ( k1_lattices('#skF_5',k2_lattices('#skF_5',B_359,'#skF_6'),'#skF_6') = '#skF_6'
      | ~ m1_subset_1(B_359,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6759,c_6752])).

tff(c_7087,plain,(
    k1_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_68,c_7032])).

tff(c_6766,plain,(
    ! [B_32,C_33] :
      ( k2_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),k1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6')) = k2_lattices('#skF_5',B_32,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5'))
      | ~ l1_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_6763])).

tff(c_6788,plain,(
    ! [B_32,C_33] :
      ( k2_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),k1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6')) = k2_lattices('#skF_5',B_32,C_33)
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_6766])).

tff(c_10632,plain,(
    ! [B_500,C_501] :
      ( k2_lattices('#skF_5',k2_lattices('#skF_5',B_500,C_501),k1_lattices('#skF_5',k2_lattices('#skF_5',B_500,C_501),'#skF_6')) = k2_lattices('#skF_5',B_500,C_501)
      | ~ m1_subset_1(C_501,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_500,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6788])).

tff(c_10773,plain,
    ( k2_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6') = k2_lattices('#skF_5','#skF_7','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7087,c_10632])).

tff(c_10846,plain,(
    k2_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6') = k2_lattices('#skF_5','#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_10773])).

tff(c_5030,plain,(
    ! [B_32,C_33] :
      ( r1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6')
      | k1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6') != '#skF_6'
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5'))
      | ~ l1_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_5026])).

tff(c_5059,plain,(
    ! [B_32,C_33] :
      ( r1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6')
      | k1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6') != '#skF_6'
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_5030])).

tff(c_5060,plain,(
    ! [B_32,C_33] :
      ( r1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6')
      | k1_lattices('#skF_5',k2_lattices('#skF_5',B_32,C_33),'#skF_6') != '#skF_6'
      | ~ m1_subset_1(C_33,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_32,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5059])).

tff(c_10868,plain,
    ( r1_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6')
    | k1_lattices('#skF_5',k2_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6'),'#skF_6') != '#skF_6'
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1(k2_lattices('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10846,c_5060])).

tff(c_10914,plain,
    ( r1_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6')
    | ~ m1_subset_1(k2_lattices('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7087,c_10846,c_10868])).

tff(c_10943,plain,(
    ~ m1_subset_1(k2_lattices('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_10914])).

tff(c_10946,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l1_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_10943])).

tff(c_10949,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_68,c_70,c_10946])).

tff(c_10951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10949])).

tff(c_10953,plain,(
    m1_subset_1(k2_lattices('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_10914])).

tff(c_10952,plain,(
    r1_lattices('#skF_5',k2_lattices('#skF_5','#skF_7','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_10914])).

tff(c_58,plain,(
    ! [C_62,B_60,A_56] :
      ( C_62 = B_60
      | ~ r1_lattices(A_56,C_62,B_60)
      | ~ r1_lattices(A_56,B_60,C_62)
      | ~ m1_subset_1(C_62,u1_struct_0(A_56))
      | ~ m1_subset_1(B_60,u1_struct_0(A_56))
      | ~ l2_lattices(A_56)
      | ~ v4_lattices(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_11214,plain,
    ( k2_lattices('#skF_5','#skF_7','#skF_6') = '#skF_6'
    | ~ r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5','#skF_7','#skF_6'))
    | ~ m1_subset_1(k2_lattices('#skF_5','#skF_7','#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | ~ v4_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10952,c_58])).

tff(c_11223,plain,
    ( k2_lattices('#skF_5','#skF_7','#skF_6') = '#skF_6'
    | ~ r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5','#skF_7','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6658,c_88,c_70,c_10953,c_11214])).

tff(c_11224,plain,
    ( k2_lattices('#skF_5','#skF_7','#skF_6') = '#skF_6'
    | ~ r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5','#skF_7','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11223])).

tff(c_11231,plain,(
    ~ r1_lattices('#skF_5','#skF_6',k2_lattices('#skF_5','#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_11224])).

tff(c_11234,plain,
    ( ~ r1_lattices('#skF_5','#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_8451,c_11231])).

tff(c_11238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5024,c_11234])).

tff(c_11239,plain,(
    k2_lattices('#skF_5','#skF_7','#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_11224])).

tff(c_6823,plain,(
    ! [A_351,B_352,C_353] :
      ( k4_lattices(A_351,B_352,C_353) = k2_lattices(A_351,B_352,C_353)
      | ~ m1_subset_1(C_353,u1_struct_0(A_351))
      | ~ m1_subset_1(B_352,u1_struct_0(A_351))
      | ~ l1_lattices(A_351)
      | ~ v6_lattices(A_351)
      | v2_struct_0(A_351) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_6839,plain,(
    ! [B_352] :
      ( k4_lattices('#skF_5',B_352,'#skF_6') = k2_lattices('#skF_5',B_352,'#skF_6')
      | ~ m1_subset_1(B_352,u1_struct_0('#skF_5'))
      | ~ l1_lattices('#skF_5')
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_6823])).

tff(c_6852,plain,(
    ! [B_352] :
      ( k4_lattices('#skF_5',B_352,'#skF_6') = k2_lattices('#skF_5',B_352,'#skF_6')
      | ~ m1_subset_1(B_352,u1_struct_0('#skF_5'))
      | ~ v6_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_6839])).

tff(c_6853,plain,(
    ! [B_352] :
      ( k4_lattices('#skF_5',B_352,'#skF_6') = k2_lattices('#skF_5',B_352,'#skF_6')
      | ~ m1_subset_1(B_352,u1_struct_0('#skF_5'))
      | ~ v6_lattices('#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6852])).

tff(c_6931,plain,(
    ~ v6_lattices('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6853])).

tff(c_6934,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_6931])).

tff(c_6937,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_6934])).

tff(c_6939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6937])).

tff(c_6942,plain,(
    ! [B_355] :
      ( k4_lattices('#skF_5',B_355,'#skF_6') = k2_lattices('#skF_5',B_355,'#skF_6')
      | ~ m1_subset_1(B_355,u1_struct_0('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_6853])).

tff(c_6997,plain,(
    k4_lattices('#skF_5','#skF_7','#skF_6') = k2_lattices('#skF_5','#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_6942])).

tff(c_11251,plain,(
    k4_lattices('#skF_5','#skF_7','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11239,c_6997])).

tff(c_74,plain,(
    v17_lattices('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_38,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k7_lattices(A_34,B_35),u1_struct_0(A_34))
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6941,plain,(
    v6_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6853])).

tff(c_7837,plain,(
    ! [A_382,B_383,C_384] :
      ( r3_lattices(A_382,B_383,C_384)
      | ~ r1_lattices(A_382,B_383,C_384)
      | ~ m1_subset_1(C_384,u1_struct_0(A_382))
      | ~ m1_subset_1(B_383,u1_struct_0(A_382))
      | ~ l3_lattices(A_382)
      | ~ v9_lattices(A_382)
      | ~ v8_lattices(A_382)
      | ~ v6_lattices(A_382)
      | v2_struct_0(A_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_14031,plain,(
    ! [A_607,B_608,B_609] :
      ( r3_lattices(A_607,B_608,k7_lattices(A_607,B_609))
      | ~ r1_lattices(A_607,B_608,k7_lattices(A_607,B_609))
      | ~ m1_subset_1(B_608,u1_struct_0(A_607))
      | ~ v9_lattices(A_607)
      | ~ v8_lattices(A_607)
      | ~ v6_lattices(A_607)
      | ~ m1_subset_1(B_609,u1_struct_0(A_607))
      | ~ l3_lattices(A_607)
      | v2_struct_0(A_607) ) ),
    inference(resolution,[status(thm)],[c_38,c_7837])).

tff(c_64,plain,(
    ~ r3_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_279])).

tff(c_14036,plain,
    ( ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6'))
    | ~ m1_subset_1(k7_lattices('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ v9_lattices('#skF_5')
    | ~ v8_lattices('#skF_5')
    | ~ v6_lattices('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_14031,c_64])).

tff(c_14040,plain,
    ( ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6'))
    | ~ m1_subset_1(k7_lattices('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_6941,c_6759,c_6757,c_14036])).

tff(c_14041,plain,
    ( ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6'))
    | ~ m1_subset_1(k7_lattices('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14040])).

tff(c_14042,plain,(
    ~ m1_subset_1(k7_lattices('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_14041])).

tff(c_14045,plain,
    ( ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_14042])).

tff(c_14048,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_14045])).

tff(c_14050,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14048])).

tff(c_14052,plain,(
    m1_subset_1(k7_lattices('#skF_5','#skF_7'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_14041])).

tff(c_6633,plain,(
    ! [A_34,B_344,B_35] :
      ( k3_lattices(A_34,B_344,k7_lattices(A_34,B_35)) = k1_lattices(A_34,B_344,k7_lattices(A_34,B_35))
      | ~ m1_subset_1(B_344,u1_struct_0(A_34))
      | ~ l2_lattices(A_34)
      | ~ v4_lattices(A_34)
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_38,c_6615])).

tff(c_14070,plain,(
    ! [B_35] :
      ( k3_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_35)) = k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_35))
      | ~ l2_lattices('#skF_5')
      | ~ v4_lattices('#skF_5')
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14052,c_6633])).

tff(c_14218,plain,(
    ! [B_35] :
      ( k3_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_35)) = k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_35))
      | ~ m1_subset_1(B_35,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_6658,c_88,c_14070])).

tff(c_20221,plain,(
    ! [B_686] :
      ( k3_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_686)) = k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_686))
      | ~ m1_subset_1(B_686,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14218])).

tff(c_62,plain,(
    ! [A_78,B_82,C_84] :
      ( k3_lattices(A_78,k7_lattices(A_78,B_82),k7_lattices(A_78,C_84)) = k7_lattices(A_78,k4_lattices(A_78,B_82,C_84))
      | ~ m1_subset_1(C_84,u1_struct_0(A_78))
      | ~ m1_subset_1(B_82,u1_struct_0(A_78))
      | ~ l3_lattices(A_78)
      | ~ v17_lattices(A_78)
      | ~ v10_lattices(A_78)
      | v2_struct_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_20230,plain,(
    ! [B_686] :
      ( k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_686)) = k7_lattices('#skF_5',k4_lattices('#skF_5','#skF_7',B_686))
      | ~ m1_subset_1(B_686,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_5'))
      | ~ l3_lattices('#skF_5')
      | ~ v17_lattices('#skF_5')
      | ~ v10_lattices('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_686,u1_struct_0('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20221,c_62])).

tff(c_20245,plain,(
    ! [B_686] :
      ( k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_686)) = k7_lattices('#skF_5',k4_lattices('#skF_5','#skF_7',B_686))
      | v2_struct_0('#skF_5')
      | ~ m1_subset_1(B_686,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_68,c_20230])).

tff(c_20253,plain,(
    ! [B_687] :
      ( k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5',B_687)) = k7_lattices('#skF_5',k4_lattices('#skF_5','#skF_7',B_687))
      | ~ m1_subset_1(B_687,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_20245])).

tff(c_122,plain,(
    ! [A_34,B_112,B_35] :
      ( r1_lattices(A_34,B_112,k7_lattices(A_34,B_35))
      | k1_lattices(A_34,B_112,k7_lattices(A_34,B_35)) != k7_lattices(A_34,B_35)
      | ~ m1_subset_1(B_112,u1_struct_0(A_34))
      | ~ l2_lattices(A_34)
      | ~ m1_subset_1(B_35,u1_struct_0(A_34))
      | ~ l3_lattices(A_34)
      | v2_struct_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_38,c_104])).

tff(c_14051,plain,(
    ~ r1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_14041])).

tff(c_14335,plain,
    ( k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6')) != k7_lattices('#skF_5','#skF_6')
    | ~ m1_subset_1(k7_lattices('#skF_5','#skF_7'),u1_struct_0('#skF_5'))
    | ~ l2_lattices('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l3_lattices('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_122,c_14051])).

tff(c_14342,plain,
    ( k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6')) != k7_lattices('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_88,c_14052,c_14335])).

tff(c_14343,plain,(
    k1_lattices('#skF_5',k7_lattices('#skF_5','#skF_7'),k7_lattices('#skF_5','#skF_6')) != k7_lattices('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_14342])).

tff(c_20266,plain,
    ( k7_lattices('#skF_5',k4_lattices('#skF_5','#skF_7','#skF_6')) != k7_lattices('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20253,c_14343])).

tff(c_20291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11251,c_20266])).

tff(c_20293,plain,(
    ~ v8_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6701])).

tff(c_20327,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_20293])).

tff(c_20330,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_20327])).

tff(c_20332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_20330])).

tff(c_20334,plain,(
    ~ v9_lattices('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6705])).

tff(c_20337,plain,
    ( ~ v10_lattices('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l3_lattices('#skF_5') ),
    inference(resolution,[status(thm)],[c_2,c_20334])).

tff(c_20340,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_76,c_20337])).

tff(c_20342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_20340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.82/4.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.99/4.45  
% 11.99/4.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.99/4.46  %$ r3_lattices > r1_lattices > m1_subset_1 > v9_lattices > v8_lattices > v7_lattices > v6_lattices > v5_lattices > v4_lattices > v2_struct_0 > v17_lattices > v10_lattices > l3_lattices > l2_lattices > l1_lattices > k4_lattices > k3_lattices > k2_lattices > k1_lattices > k7_lattices > #nlpp > u1_struct_0 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3
% 11.99/4.46  
% 11.99/4.46  %Foreground sorts:
% 11.99/4.46  
% 11.99/4.46  
% 11.99/4.46  %Background operators:
% 11.99/4.46  
% 11.99/4.46  
% 11.99/4.46  %Foreground operators:
% 11.99/4.46  tff(l3_lattices, type, l3_lattices: $i > $o).
% 11.99/4.46  tff(k3_lattices, type, k3_lattices: ($i * $i * $i) > $i).
% 11.99/4.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.99/4.46  tff(k2_lattices, type, k2_lattices: ($i * $i * $i) > $i).
% 11.99/4.46  tff(l2_lattices, type, l2_lattices: $i > $o).
% 11.99/4.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.99/4.46  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.99/4.46  tff(r3_lattices, type, r3_lattices: ($i * $i * $i) > $o).
% 11.99/4.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.99/4.46  tff(k4_lattices, type, k4_lattices: ($i * $i * $i) > $i).
% 11.99/4.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 11.99/4.46  tff(k1_lattices, type, k1_lattices: ($i * $i * $i) > $i).
% 11.99/4.46  tff(l1_lattices, type, l1_lattices: $i > $o).
% 11.99/4.46  tff('#skF_7', type, '#skF_7': $i).
% 11.99/4.46  tff(r1_lattices, type, r1_lattices: ($i * $i * $i) > $o).
% 11.99/4.46  tff(v17_lattices, type, v17_lattices: $i > $o).
% 11.99/4.46  tff('#skF_5', type, '#skF_5': $i).
% 11.99/4.46  tff(v4_lattices, type, v4_lattices: $i > $o).
% 11.99/4.46  tff('#skF_6', type, '#skF_6': $i).
% 11.99/4.46  tff(v6_lattices, type, v6_lattices: $i > $o).
% 11.99/4.46  tff(v9_lattices, type, v9_lattices: $i > $o).
% 11.99/4.46  tff(v5_lattices, type, v5_lattices: $i > $o).
% 11.99/4.46  tff(v10_lattices, type, v10_lattices: $i > $o).
% 11.99/4.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.99/4.46  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.99/4.46  tff(v8_lattices, type, v8_lattices: $i > $o).
% 11.99/4.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.99/4.46  tff(k7_lattices, type, k7_lattices: ($i * $i) > $i).
% 11.99/4.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.99/4.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.99/4.46  tff(v7_lattices, type, v7_lattices: $i > $o).
% 11.99/4.46  
% 12.13/4.50  tff(f_279, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_lattices(A, B, C) => r3_lattices(A, k7_lattices(A, C), k7_lattices(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_lattices)).
% 12.13/4.50  tff(f_47, axiom, (![A]: (l3_lattices(A) => ((~v2_struct_0(A) & v10_lattices(A)) => ((((((~v2_struct_0(A) & v4_lattices(A)) & v5_lattices(A)) & v6_lattices(A)) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattices)).
% 12.13/4.50  tff(f_118, axiom, (![A]: (l3_lattices(A) => (l1_lattices(A) & l2_lattices(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l3_lattices)).
% 12.13/4.50  tff(f_62, axiom, (![A]: ((~v2_struct_0(A) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k1_lattices(A, B, C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_lattices)).
% 12.13/4.50  tff(f_77, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v8_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k1_lattices(A, k2_lattices(A, B, C), C) = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_lattices)).
% 12.13/4.50  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l3_lattices(A)) => (v9_lattices(A) <=> (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k2_lattices(A, B, k1_lattices(A, B, C)) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_lattices)).
% 12.13/4.50  tff(f_199, axiom, (![A]: ((((~v2_struct_0(A) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattices(A, B, C) <=> (k2_lattices(A, B, C) = B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_lattices)).
% 12.13/4.50  tff(f_180, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_lattices(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_lattices)).
% 12.13/4.50  tff(f_163, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v6_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_lattices(A, B, C) <=> r1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_lattices)).
% 12.13/4.50  tff(f_131, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k3_lattices(A, B, C) = k1_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_lattices)).
% 12.13/4.50  tff(f_242, axiom, (![A]: (((((~v2_struct_0(A) & v7_lattices(A)) & v8_lattices(A)) & v9_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattices(A, B, C) => r1_lattices(A, k2_lattices(A, B, D), k2_lattices(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_lattices)).
% 12.13/4.50  tff(f_144, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v6_lattices(A)) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k4_lattices(A, B, C) = k2_lattices(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_lattices)).
% 12.13/4.50  tff(f_103, axiom, (![A, B, C]: ((((~v2_struct_0(A) & l1_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k2_lattices(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_lattices)).
% 12.13/4.50  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v4_lattices(A)) & l2_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_lattices(A, B, C) & r1_lattices(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_lattices)).
% 12.13/4.50  tff(f_112, axiom, (![A, B]: (((~v2_struct_0(A) & l3_lattices(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k7_lattices(A, B), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_lattices)).
% 12.13/4.50  tff(f_259, axiom, (![A]: ((((~v2_struct_0(A) & v10_lattices(A)) & v17_lattices(A)) & l3_lattices(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k7_lattices(A, k4_lattices(A, B, C)) = k3_lattices(A, k7_lattices(A, B), k7_lattices(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_lattices)).
% 12.13/4.50  tff(c_78, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_72, plain, (l3_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_76, plain, (v10_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_2, plain, (![A_1]: (v9_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.13/4.50  tff(c_4, plain, (![A_1]: (v8_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.13/4.50  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_68, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_84, plain, (![A_90]: (l2_lattices(A_90) | ~l3_lattices(A_90))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.13/4.50  tff(c_88, plain, (l2_lattices('#skF_5')), inference(resolution, [status(thm)], [c_72, c_84])).
% 12.13/4.50  tff(c_104, plain, (![A_111, B_112, C_113]: (r1_lattices(A_111, B_112, C_113) | k1_lattices(A_111, B_112, C_113)!=C_113 | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l2_lattices(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.13/4.50  tff(c_118, plain, (![B_112]: (r1_lattices('#skF_5', B_112, '#skF_7') | k1_lattices('#skF_5', B_112, '#skF_7')!='#skF_7' | ~m1_subset_1(B_112, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_104])).
% 12.13/4.50  tff(c_129, plain, (![B_112]: (r1_lattices('#skF_5', B_112, '#skF_7') | k1_lattices('#skF_5', B_112, '#skF_7')!='#skF_7' | ~m1_subset_1(B_112, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_118])).
% 12.13/4.50  tff(c_135, plain, (![B_114]: (r1_lattices('#skF_5', B_114, '#skF_7') | k1_lattices('#skF_5', B_114, '#skF_7')!='#skF_7' | ~m1_subset_1(B_114, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_129])).
% 12.13/4.50  tff(c_191, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7') | k1_lattices('#skF_5', '#skF_6', '#skF_7')!='#skF_7'), inference(resolution, [status(thm)], [c_70, c_135])).
% 12.13/4.50  tff(c_3865, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_7')!='#skF_7'), inference(splitLeft, [status(thm)], [c_191])).
% 12.13/4.50  tff(c_3970, plain, (![A_251, B_252, C_253]: (k1_lattices(A_251, k2_lattices(A_251, B_252, C_253), C_253)=C_253 | ~m1_subset_1(C_253, u1_struct_0(A_251)) | ~m1_subset_1(B_252, u1_struct_0(A_251)) | ~v8_lattices(A_251) | ~l3_lattices(A_251) | v2_struct_0(A_251))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.13/4.50  tff(c_3984, plain, (![B_252]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_252, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_252, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_3970])).
% 12.13/4.50  tff(c_3995, plain, (![B_252]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_252, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_252, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3984])).
% 12.13/4.50  tff(c_3996, plain, (![B_252]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_252, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_252, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_3995])).
% 12.13/4.50  tff(c_4037, plain, (~v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_3996])).
% 12.13/4.50  tff(c_4041, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_4037])).
% 12.13/4.50  tff(c_4044, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_4041])).
% 12.13/4.50  tff(c_4046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4044])).
% 12.13/4.50  tff(c_4048, plain, (v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_3996])).
% 12.13/4.50  tff(c_32, plain, (![A_20]: (m1_subset_1('#skF_4'(A_20), u1_struct_0(A_20)) | v9_lattices(A_20) | ~l3_lattices(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.13/4.50  tff(c_4049, plain, (![B_257]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_257, '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1(B_257, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_3996])).
% 12.13/4.50  tff(c_4065, plain, (k1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7'), '#skF_7')='#skF_7' | v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_4049])).
% 12.13/4.50  tff(c_4094, plain, (k1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7'), '#skF_7')='#skF_7' | v9_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4065])).
% 12.13/4.50  tff(c_4095, plain, (k1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7'), '#skF_7')='#skF_7' | v9_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_4094])).
% 12.13/4.50  tff(c_4145, plain, (v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_4095])).
% 12.13/4.50  tff(c_4798, plain, (![A_280, B_281, C_282]: (r1_lattices(A_280, B_281, C_282) | k2_lattices(A_280, B_281, C_282)!=B_281 | ~m1_subset_1(C_282, u1_struct_0(A_280)) | ~m1_subset_1(B_281, u1_struct_0(A_280)) | ~l3_lattices(A_280) | ~v9_lattices(A_280) | ~v8_lattices(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_199])).
% 12.13/4.50  tff(c_4812, plain, (![B_281]: (r1_lattices('#skF_5', B_281, '#skF_7') | k2_lattices('#skF_5', B_281, '#skF_7')!=B_281 | ~m1_subset_1(B_281, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_4798])).
% 12.13/4.50  tff(c_4823, plain, (![B_281]: (r1_lattices('#skF_5', B_281, '#skF_7') | k2_lattices('#skF_5', B_281, '#skF_7')!=B_281 | ~m1_subset_1(B_281, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4048, c_4145, c_72, c_4812])).
% 12.13/4.50  tff(c_4829, plain, (![B_283]: (r1_lattices('#skF_5', B_283, '#skF_7') | k2_lattices('#skF_5', B_283, '#skF_7')!=B_283 | ~m1_subset_1(B_283, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_4823])).
% 12.13/4.50  tff(c_4887, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7') | k2_lattices('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(resolution, [status(thm)], [c_70, c_4829])).
% 12.13/4.50  tff(c_4888, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(splitLeft, [status(thm)], [c_4887])).
% 12.13/4.50  tff(c_8, plain, (![A_1]: (v6_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.13/4.50  tff(c_4288, plain, (![A_263, B_264, C_265]: (r3_lattices(A_263, B_264, B_264) | ~m1_subset_1(C_265, u1_struct_0(A_263)) | ~m1_subset_1(B_264, u1_struct_0(A_263)) | ~l3_lattices(A_263) | ~v9_lattices(A_263) | ~v8_lattices(A_263) | ~v6_lattices(A_263) | v2_struct_0(A_263))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.13/4.50  tff(c_4302, plain, (![B_264]: (r3_lattices('#skF_5', B_264, B_264) | ~m1_subset_1(B_264, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_4288])).
% 12.13/4.50  tff(c_4313, plain, (![B_264]: (r3_lattices('#skF_5', B_264, B_264) | ~m1_subset_1(B_264, u1_struct_0('#skF_5')) | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4048, c_4145, c_72, c_4302])).
% 12.13/4.50  tff(c_4314, plain, (![B_264]: (r3_lattices('#skF_5', B_264, B_264) | ~m1_subset_1(B_264, u1_struct_0('#skF_5')) | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_4313])).
% 12.13/4.50  tff(c_4319, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_4314])).
% 12.13/4.50  tff(c_4322, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_4319])).
% 12.13/4.50  tff(c_4325, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_4322])).
% 12.13/4.50  tff(c_4327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4325])).
% 12.13/4.50  tff(c_4329, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_4314])).
% 12.13/4.50  tff(c_66, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_4957, plain, (![A_286, B_287, C_288]: (r1_lattices(A_286, B_287, C_288) | ~r3_lattices(A_286, B_287, C_288) | ~m1_subset_1(C_288, u1_struct_0(A_286)) | ~m1_subset_1(B_287, u1_struct_0(A_286)) | ~l3_lattices(A_286) | ~v9_lattices(A_286) | ~v8_lattices(A_286) | ~v6_lattices(A_286) | v2_struct_0(A_286))), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.13/4.50  tff(c_4965, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_4957])).
% 12.13/4.50  tff(c_4980, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4329, c_4048, c_4145, c_72, c_70, c_68, c_4965])).
% 12.13/4.50  tff(c_4981, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_78, c_4980])).
% 12.13/4.50  tff(c_56, plain, (![A_49, B_53, C_55]: (k2_lattices(A_49, B_53, C_55)=B_53 | ~r1_lattices(A_49, B_53, C_55) | ~m1_subset_1(C_55, u1_struct_0(A_49)) | ~m1_subset_1(B_53, u1_struct_0(A_49)) | ~l3_lattices(A_49) | ~v9_lattices(A_49) | ~v8_lattices(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_199])).
% 12.13/4.50  tff(c_4983, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_7')='#skF_6' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4981, c_56])).
% 12.13/4.50  tff(c_4990, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_7')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4048, c_4145, c_72, c_70, c_68, c_4983])).
% 12.13/4.50  tff(c_4992, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_4888, c_4990])).
% 12.13/4.50  tff(c_4993, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_4887])).
% 12.13/4.50  tff(c_18, plain, (![A_2, B_6, C_8]: (k1_lattices(A_2, B_6, C_8)=C_8 | ~r1_lattices(A_2, B_6, C_8) | ~m1_subset_1(C_8, u1_struct_0(A_2)) | ~m1_subset_1(B_6, u1_struct_0(A_2)) | ~l2_lattices(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.13/4.50  tff(c_5000, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_4993, c_18])).
% 12.13/4.50  tff(c_5011, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_7')='#skF_7' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_70, c_68, c_5000])).
% 12.13/4.50  tff(c_5013, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3865, c_5011])).
% 12.13/4.50  tff(c_5015, plain, (~v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_4095])).
% 12.13/4.50  tff(c_5018, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_5015])).
% 12.13/4.50  tff(c_5021, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_5018])).
% 12.13/4.50  tff(c_5023, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5021])).
% 12.13/4.50  tff(c_5024, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_191])).
% 12.13/4.50  tff(c_6, plain, (![A_1]: (v7_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.13/4.50  tff(c_26, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), u1_struct_0(A_9)) | v8_lattices(A_9) | ~l3_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.13/4.50  tff(c_12, plain, (![A_1]: (v4_lattices(A_1) | ~v10_lattices(A_1) | v2_struct_0(A_1) | ~l3_lattices(A_1))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.13/4.50  tff(c_6615, plain, (![A_343, B_344, C_345]: (k3_lattices(A_343, B_344, C_345)=k1_lattices(A_343, B_344, C_345) | ~m1_subset_1(C_345, u1_struct_0(A_343)) | ~m1_subset_1(B_344, u1_struct_0(A_343)) | ~l2_lattices(A_343) | ~v4_lattices(A_343) | v2_struct_0(A_343))), inference(cnfTransformation, [status(thm)], [f_131])).
% 12.13/4.50  tff(c_6629, plain, (![B_344]: (k3_lattices('#skF_5', B_344, '#skF_7')=k1_lattices('#skF_5', B_344, '#skF_7') | ~m1_subset_1(B_344, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | ~v4_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_6615])).
% 12.13/4.50  tff(c_6640, plain, (![B_344]: (k3_lattices('#skF_5', B_344, '#skF_7')=k1_lattices('#skF_5', B_344, '#skF_7') | ~m1_subset_1(B_344, u1_struct_0('#skF_5')) | ~v4_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_6629])).
% 12.13/4.50  tff(c_6641, plain, (![B_344]: (k3_lattices('#skF_5', B_344, '#skF_7')=k1_lattices('#skF_5', B_344, '#skF_7') | ~m1_subset_1(B_344, u1_struct_0('#skF_5')) | ~v4_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6640])).
% 12.13/4.50  tff(c_6648, plain, (~v4_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_6641])).
% 12.13/4.50  tff(c_6651, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_12, c_6648])).
% 12.13/4.50  tff(c_6654, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_6651])).
% 12.13/4.50  tff(c_6656, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6654])).
% 12.13/4.50  tff(c_6659, plain, (![B_346]: (k3_lattices('#skF_5', B_346, '#skF_7')=k1_lattices('#skF_5', B_346, '#skF_7') | ~m1_subset_1(B_346, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_6641])).
% 12.13/4.50  tff(c_6671, plain, (k3_lattices('#skF_5', '#skF_1'('#skF_5'), '#skF_7')=k1_lattices('#skF_5', '#skF_1'('#skF_5'), '#skF_7') | v8_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_6659])).
% 12.13/4.50  tff(c_6700, plain, (k3_lattices('#skF_5', '#skF_1'('#skF_5'), '#skF_7')=k1_lattices('#skF_5', '#skF_1'('#skF_5'), '#skF_7') | v8_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6671])).
% 12.13/4.50  tff(c_6701, plain, (k3_lattices('#skF_5', '#skF_1'('#skF_5'), '#skF_7')=k1_lattices('#skF_5', '#skF_1'('#skF_5'), '#skF_7') | v8_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_6700])).
% 12.13/4.50  tff(c_6759, plain, (v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_6701])).
% 12.13/4.50  tff(c_6675, plain, (k3_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7')=k1_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7') | v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_32, c_6659])).
% 12.13/4.50  tff(c_6704, plain, (k3_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7')=k1_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7') | v9_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6675])).
% 12.13/4.50  tff(c_6705, plain, (k3_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7')=k1_lattices('#skF_5', '#skF_4'('#skF_5'), '#skF_7') | v9_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_6704])).
% 12.13/4.50  tff(c_6757, plain, (v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_6705])).
% 12.13/4.50  tff(c_5025, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_191])).
% 12.13/4.50  tff(c_6580, plain, (![A_340, B_341, C_342]: (k2_lattices(A_340, B_341, k1_lattices(A_340, B_341, C_342))=B_341 | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~m1_subset_1(B_341, u1_struct_0(A_340)) | ~v9_lattices(A_340) | ~l3_lattices(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.13/4.50  tff(c_6594, plain, (![B_341]: (k2_lattices('#skF_5', B_341, k1_lattices('#skF_5', B_341, '#skF_7'))=B_341 | ~m1_subset_1(B_341, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_6580])).
% 12.13/4.50  tff(c_6605, plain, (![B_341]: (k2_lattices('#skF_5', B_341, k1_lattices('#skF_5', B_341, '#skF_7'))=B_341 | ~m1_subset_1(B_341, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6594])).
% 12.13/4.50  tff(c_6606, plain, (![B_341]: (k2_lattices('#skF_5', B_341, k1_lattices('#skF_5', B_341, '#skF_7'))=B_341 | ~m1_subset_1(B_341, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6605])).
% 12.13/4.50  tff(c_7164, plain, (![B_361]: (k2_lattices('#skF_5', B_361, k1_lattices('#skF_5', B_361, '#skF_7'))=B_361 | ~m1_subset_1(B_361, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_6606])).
% 12.13/4.50  tff(c_7186, plain, (k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_7'))='#skF_6'), inference(resolution, [status(thm)], [c_70, c_7164])).
% 12.13/4.50  tff(c_7214, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5025, c_7186])).
% 12.13/4.50  tff(c_8302, plain, (![A_409, B_410, D_411, C_412]: (r1_lattices(A_409, k2_lattices(A_409, B_410, D_411), k2_lattices(A_409, C_412, D_411)) | ~r1_lattices(A_409, B_410, C_412) | ~m1_subset_1(D_411, u1_struct_0(A_409)) | ~m1_subset_1(C_412, u1_struct_0(A_409)) | ~m1_subset_1(B_410, u1_struct_0(A_409)) | ~l3_lattices(A_409) | ~v9_lattices(A_409) | ~v8_lattices(A_409) | ~v7_lattices(A_409) | v2_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_242])).
% 12.13/4.50  tff(c_8323, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_7')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v7_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7214, c_8302])).
% 12.13/4.50  tff(c_8361, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_7')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')) | ~v7_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6759, c_6757, c_72, c_70, c_68, c_8323])).
% 12.13/4.50  tff(c_8362, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_7')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')) | ~v7_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_8361])).
% 12.13/4.50  tff(c_8384, plain, (~v7_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_8362])).
% 12.13/4.50  tff(c_8387, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_6, c_8384])).
% 12.13/4.50  tff(c_8390, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_8387])).
% 12.13/4.50  tff(c_8392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_8390])).
% 12.13/4.50  tff(c_8394, plain, (v7_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_8362])).
% 12.13/4.50  tff(c_120, plain, (![B_112]: (r1_lattices('#skF_5', B_112, '#skF_6') | k1_lattices('#skF_5', B_112, '#skF_6')!='#skF_6' | ~m1_subset_1(B_112, u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_104])).
% 12.13/4.50  tff(c_133, plain, (![B_112]: (r1_lattices('#skF_5', B_112, '#skF_6') | k1_lattices('#skF_5', B_112, '#skF_6')!='#skF_6' | ~m1_subset_1(B_112, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_120])).
% 12.13/4.50  tff(c_5026, plain, (![B_289]: (r1_lattices('#skF_5', B_289, '#skF_6') | k1_lattices('#skF_5', B_289, '#skF_6')!='#skF_6' | ~m1_subset_1(B_289, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_133])).
% 12.13/4.50  tff(c_5082, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | k1_lattices('#skF_5', '#skF_6', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_70, c_5026])).
% 12.13/4.50  tff(c_5137, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')!='#skF_6'), inference(splitLeft, [status(thm)], [c_5082])).
% 12.13/4.50  tff(c_24, plain, (![A_9]: (m1_subset_1('#skF_2'(A_9), u1_struct_0(A_9)) | v8_lattices(A_9) | ~l3_lattices(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.13/4.50  tff(c_5176, plain, (![A_296, B_297, C_298]: (k2_lattices(A_296, B_297, k1_lattices(A_296, B_297, C_298))=B_297 | ~m1_subset_1(C_298, u1_struct_0(A_296)) | ~m1_subset_1(B_297, u1_struct_0(A_296)) | ~v9_lattices(A_296) | ~l3_lattices(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.13/4.50  tff(c_5190, plain, (![B_297]: (k2_lattices('#skF_5', B_297, k1_lattices('#skF_5', B_297, '#skF_7'))=B_297 | ~m1_subset_1(B_297, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_5176])).
% 12.13/4.50  tff(c_5201, plain, (![B_297]: (k2_lattices('#skF_5', B_297, k1_lattices('#skF_5', B_297, '#skF_7'))=B_297 | ~m1_subset_1(B_297, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5190])).
% 12.13/4.50  tff(c_5202, plain, (![B_297]: (k2_lattices('#skF_5', B_297, k1_lattices('#skF_5', B_297, '#skF_7'))=B_297 | ~m1_subset_1(B_297, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_5201])).
% 12.13/4.50  tff(c_5208, plain, (~v9_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_5202])).
% 12.13/4.50  tff(c_5211, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_5208])).
% 12.13/4.50  tff(c_5214, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_5211])).
% 12.13/4.50  tff(c_5216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5214])).
% 12.13/4.50  tff(c_5219, plain, (![B_299]: (k2_lattices('#skF_5', B_299, k1_lattices('#skF_5', B_299, '#skF_7'))=B_299 | ~m1_subset_1(B_299, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_5202])).
% 12.13/4.50  tff(c_5234, plain, (k2_lattices('#skF_5', '#skF_2'('#skF_5'), k1_lattices('#skF_5', '#skF_2'('#skF_5'), '#skF_7'))='#skF_2'('#skF_5') | v8_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_5219])).
% 12.13/4.50  tff(c_5260, plain, (k2_lattices('#skF_5', '#skF_2'('#skF_5'), k1_lattices('#skF_5', '#skF_2'('#skF_5'), '#skF_7'))='#skF_2'('#skF_5') | v8_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5234])).
% 12.13/4.50  tff(c_5261, plain, (k2_lattices('#skF_5', '#skF_2'('#skF_5'), k1_lattices('#skF_5', '#skF_2'('#skF_5'), '#skF_7'))='#skF_2'('#skF_5') | v8_lattices('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_78, c_5260])).
% 12.13/4.50  tff(c_5321, plain, (v8_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_5261])).
% 12.13/4.50  tff(c_5218, plain, (v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_5202])).
% 12.13/4.50  tff(c_5934, plain, (![A_322, B_323, C_324]: (r1_lattices(A_322, B_323, C_324) | k2_lattices(A_322, B_323, C_324)!=B_323 | ~m1_subset_1(C_324, u1_struct_0(A_322)) | ~m1_subset_1(B_323, u1_struct_0(A_322)) | ~l3_lattices(A_322) | ~v9_lattices(A_322) | ~v8_lattices(A_322) | v2_struct_0(A_322))), inference(cnfTransformation, [status(thm)], [f_199])).
% 12.13/4.50  tff(c_5950, plain, (![B_323]: (r1_lattices('#skF_5', B_323, '#skF_6') | k2_lattices('#skF_5', B_323, '#skF_6')!=B_323 | ~m1_subset_1(B_323, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_5934])).
% 12.13/4.50  tff(c_5963, plain, (![B_323]: (r1_lattices('#skF_5', B_323, '#skF_6') | k2_lattices('#skF_5', B_323, '#skF_6')!=B_323 | ~m1_subset_1(B_323, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_5321, c_5218, c_72, c_5950])).
% 12.13/4.50  tff(c_6026, plain, (![B_326]: (r1_lattices('#skF_5', B_326, '#skF_6') | k2_lattices('#skF_5', B_326, '#skF_6')!=B_326 | ~m1_subset_1(B_326, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_5963])).
% 12.13/4.50  tff(c_6084, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | k2_lattices('#skF_5', '#skF_6', '#skF_6')!='#skF_6'), inference(resolution, [status(thm)], [c_70, c_6026])).
% 12.13/4.50  tff(c_6085, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_6')!='#skF_6'), inference(splitLeft, [status(thm)], [c_6084])).
% 12.13/4.50  tff(c_79, plain, (![A_89]: (l1_lattices(A_89) | ~l3_lattices(A_89))), inference(cnfTransformation, [status(thm)], [f_118])).
% 12.13/4.50  tff(c_83, plain, (l1_lattices('#skF_5')), inference(resolution, [status(thm)], [c_72, c_79])).
% 12.13/4.50  tff(c_5290, plain, (![A_300, B_301, C_302]: (k4_lattices(A_300, B_301, C_302)=k2_lattices(A_300, B_301, C_302) | ~m1_subset_1(C_302, u1_struct_0(A_300)) | ~m1_subset_1(B_301, u1_struct_0(A_300)) | ~l1_lattices(A_300) | ~v6_lattices(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.13/4.50  tff(c_5306, plain, (![B_301]: (k4_lattices('#skF_5', B_301, '#skF_6')=k2_lattices('#skF_5', B_301, '#skF_6') | ~m1_subset_1(B_301, u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_5290])).
% 12.13/4.50  tff(c_5319, plain, (![B_301]: (k4_lattices('#skF_5', B_301, '#skF_6')=k2_lattices('#skF_5', B_301, '#skF_6') | ~m1_subset_1(B_301, u1_struct_0('#skF_5')) | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_5306])).
% 12.13/4.50  tff(c_5320, plain, (![B_301]: (k4_lattices('#skF_5', B_301, '#skF_6')=k2_lattices('#skF_5', B_301, '#skF_6') | ~m1_subset_1(B_301, u1_struct_0('#skF_5')) | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_5319])).
% 12.13/4.50  tff(c_5384, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_5320])).
% 12.13/4.50  tff(c_5387, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_5384])).
% 12.13/4.50  tff(c_5390, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_5387])).
% 12.13/4.50  tff(c_5392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5390])).
% 12.13/4.50  tff(c_5394, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_5320])).
% 12.13/4.50  tff(c_5104, plain, (![A_290, B_291, C_292]: (r3_lattices(A_290, B_291, B_291) | ~m1_subset_1(C_292, u1_struct_0(A_290)) | ~m1_subset_1(B_291, u1_struct_0(A_290)) | ~l3_lattices(A_290) | ~v9_lattices(A_290) | ~v8_lattices(A_290) | ~v6_lattices(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_180])).
% 12.13/4.50  tff(c_5120, plain, (![B_291]: (r3_lattices('#skF_5', B_291, B_291) | ~m1_subset_1(B_291, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_5104])).
% 12.13/4.50  tff(c_5133, plain, (![B_291]: (r3_lattices('#skF_5', B_291, B_291) | ~m1_subset_1(B_291, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_5120])).
% 12.13/4.50  tff(c_5134, plain, (![B_291]: (r3_lattices('#skF_5', B_291, B_291) | ~m1_subset_1(B_291, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_5133])).
% 12.13/4.50  tff(c_5493, plain, (![B_308]: (r3_lattices('#skF_5', B_308, B_308) | ~m1_subset_1(B_308, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_5394, c_5321, c_5218, c_5134])).
% 12.13/4.50  tff(c_5541, plain, (r3_lattices('#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_5493])).
% 12.13/4.50  tff(c_6497, plain, (![A_337, B_338, C_339]: (r1_lattices(A_337, B_338, C_339) | ~r3_lattices(A_337, B_338, C_339) | ~m1_subset_1(C_339, u1_struct_0(A_337)) | ~m1_subset_1(B_338, u1_struct_0(A_337)) | ~l3_lattices(A_337) | ~v9_lattices(A_337) | ~v8_lattices(A_337) | ~v6_lattices(A_337) | v2_struct_0(A_337))), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.13/4.50  tff(c_6501, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_5541, c_6497])).
% 12.13/4.50  tff(c_6512, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5394, c_5321, c_5218, c_72, c_70, c_6501])).
% 12.13/4.50  tff(c_6513, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_6512])).
% 12.13/4.50  tff(c_6523, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6513, c_56])).
% 12.13/4.50  tff(c_6530, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5321, c_5218, c_72, c_70, c_6523])).
% 12.13/4.50  tff(c_6532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6085, c_6530])).
% 12.13/4.50  tff(c_6533, plain, (r1_lattices('#skF_5', '#skF_6', '#skF_6')), inference(splitRight, [status(thm)], [c_6084])).
% 12.13/4.50  tff(c_6540, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6533, c_18])).
% 12.13/4.50  tff(c_6552, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6' | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_70, c_6540])).
% 12.13/4.50  tff(c_6554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_5137, c_6552])).
% 12.13/4.50  tff(c_6556, plain, (~v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_5261])).
% 12.13/4.50  tff(c_6559, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_6556])).
% 12.13/4.50  tff(c_6562, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_6559])).
% 12.13/4.50  tff(c_6564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6562])).
% 12.13/4.50  tff(c_6566, plain, (k1_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_5082])).
% 12.13/4.50  tff(c_6596, plain, (![B_341]: (k2_lattices('#skF_5', B_341, k1_lattices('#skF_5', B_341, '#skF_6'))=B_341 | ~m1_subset_1(B_341, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_6580])).
% 12.13/4.50  tff(c_6609, plain, (![B_341]: (k2_lattices('#skF_5', B_341, k1_lattices('#skF_5', B_341, '#skF_6'))=B_341 | ~m1_subset_1(B_341, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6596])).
% 12.13/4.50  tff(c_6610, plain, (![B_341]: (k2_lattices('#skF_5', B_341, k1_lattices('#skF_5', B_341, '#skF_6'))=B_341 | ~m1_subset_1(B_341, u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6609])).
% 12.13/4.50  tff(c_6763, plain, (![B_350]: (k2_lattices('#skF_5', B_350, k1_lattices('#skF_5', B_350, '#skF_6'))=B_350 | ~m1_subset_1(B_350, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_6757, c_6610])).
% 12.13/4.50  tff(c_6785, plain, (k2_lattices('#skF_5', '#skF_6', k1_lattices('#skF_5', '#skF_6', '#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_70, c_6763])).
% 12.13/4.50  tff(c_6812, plain, (k2_lattices('#skF_5', '#skF_6', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6566, c_6785])).
% 12.13/4.50  tff(c_8341, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_6')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v7_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_6812, c_8302])).
% 12.13/4.50  tff(c_8379, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_6')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')) | ~v7_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6759, c_6757, c_72, c_70, c_70, c_8341])).
% 12.13/4.50  tff(c_8380, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_6')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')) | ~v7_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_8379])).
% 12.13/4.50  tff(c_8451, plain, (![C_412]: (r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', C_412, '#skF_6')) | ~r1_lattices('#skF_5', '#skF_6', C_412) | ~m1_subset_1(C_412, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_8394, c_8380])).
% 12.13/4.50  tff(c_6658, plain, (v4_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_6641])).
% 12.13/4.50  tff(c_36, plain, (![A_31, B_32, C_33]: (m1_subset_1(k2_lattices(A_31, B_32, C_33), u1_struct_0(A_31)) | ~m1_subset_1(C_33, u1_struct_0(A_31)) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_lattices(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.13/4.50  tff(c_6722, plain, (![A_347, B_348, C_349]: (k1_lattices(A_347, k2_lattices(A_347, B_348, C_349), C_349)=C_349 | ~m1_subset_1(C_349, u1_struct_0(A_347)) | ~m1_subset_1(B_348, u1_struct_0(A_347)) | ~v8_lattices(A_347) | ~l3_lattices(A_347) | v2_struct_0(A_347))), inference(cnfTransformation, [status(thm)], [f_77])).
% 12.13/4.50  tff(c_6738, plain, (![B_348]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_348, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_348, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_6722])).
% 12.13/4.50  tff(c_6751, plain, (![B_348]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_348, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_348, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6738])).
% 12.13/4.50  tff(c_6752, plain, (![B_348]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_348, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_348, u1_struct_0('#skF_5')) | ~v8_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6751])).
% 12.13/4.50  tff(c_7032, plain, (![B_359]: (k1_lattices('#skF_5', k2_lattices('#skF_5', B_359, '#skF_6'), '#skF_6')='#skF_6' | ~m1_subset_1(B_359, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_6759, c_6752])).
% 12.13/4.50  tff(c_7087, plain, (k1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_68, c_7032])).
% 12.13/4.50  tff(c_6766, plain, (![B_32, C_33]: (k2_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), k1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6'))=k2_lattices('#skF_5', B_32, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_5')) | ~m1_subset_1(B_32, u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_6763])).
% 12.13/4.50  tff(c_6788, plain, (![B_32, C_33]: (k2_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), k1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6'))=k2_lattices('#skF_5', B_32, C_33) | ~m1_subset_1(C_33, u1_struct_0('#skF_5')) | ~m1_subset_1(B_32, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_6766])).
% 12.13/4.50  tff(c_10632, plain, (![B_500, C_501]: (k2_lattices('#skF_5', k2_lattices('#skF_5', B_500, C_501), k1_lattices('#skF_5', k2_lattices('#skF_5', B_500, C_501), '#skF_6'))=k2_lattices('#skF_5', B_500, C_501) | ~m1_subset_1(C_501, u1_struct_0('#skF_5')) | ~m1_subset_1(B_500, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_6788])).
% 12.13/4.50  tff(c_10773, plain, (k2_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6')=k2_lattices('#skF_5', '#skF_7', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7087, c_10632])).
% 12.13/4.50  tff(c_10846, plain, (k2_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6')=k2_lattices('#skF_5', '#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_10773])).
% 12.13/4.50  tff(c_5030, plain, (![B_32, C_33]: (r1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6') | k1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6')!='#skF_6' | ~m1_subset_1(C_33, u1_struct_0('#skF_5')) | ~m1_subset_1(B_32, u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_5026])).
% 12.13/4.50  tff(c_5059, plain, (![B_32, C_33]: (r1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6') | k1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6')!='#skF_6' | ~m1_subset_1(C_33, u1_struct_0('#skF_5')) | ~m1_subset_1(B_32, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_5030])).
% 12.13/4.50  tff(c_5060, plain, (![B_32, C_33]: (r1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6') | k1_lattices('#skF_5', k2_lattices('#skF_5', B_32, C_33), '#skF_6')!='#skF_6' | ~m1_subset_1(C_33, u1_struct_0('#skF_5')) | ~m1_subset_1(B_32, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_5059])).
% 12.13/4.50  tff(c_10868, plain, (r1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6') | k1_lattices('#skF_5', k2_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6'), '#skF_6')!='#skF_6' | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1(k2_lattices('#skF_5', '#skF_7', '#skF_6'), u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_10846, c_5060])).
% 12.13/4.50  tff(c_10914, plain, (r1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6') | ~m1_subset_1(k2_lattices('#skF_5', '#skF_7', '#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_7087, c_10846, c_10868])).
% 12.13/4.50  tff(c_10943, plain, (~m1_subset_1(k2_lattices('#skF_5', '#skF_7', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_10914])).
% 12.13/4.50  tff(c_10946, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_10943])).
% 12.13/4.50  tff(c_10949, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_68, c_70, c_10946])).
% 12.13/4.50  tff(c_10951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_10949])).
% 12.13/4.50  tff(c_10953, plain, (m1_subset_1(k2_lattices('#skF_5', '#skF_7', '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_10914])).
% 12.13/4.50  tff(c_10952, plain, (r1_lattices('#skF_5', k2_lattices('#skF_5', '#skF_7', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_10914])).
% 12.13/4.50  tff(c_58, plain, (![C_62, B_60, A_56]: (C_62=B_60 | ~r1_lattices(A_56, C_62, B_60) | ~r1_lattices(A_56, B_60, C_62) | ~m1_subset_1(C_62, u1_struct_0(A_56)) | ~m1_subset_1(B_60, u1_struct_0(A_56)) | ~l2_lattices(A_56) | ~v4_lattices(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_218])).
% 12.13/4.50  tff(c_11214, plain, (k2_lattices('#skF_5', '#skF_7', '#skF_6')='#skF_6' | ~r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', '#skF_7', '#skF_6')) | ~m1_subset_1(k2_lattices('#skF_5', '#skF_7', '#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | ~v4_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_10952, c_58])).
% 12.13/4.50  tff(c_11223, plain, (k2_lattices('#skF_5', '#skF_7', '#skF_6')='#skF_6' | ~r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', '#skF_7', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6658, c_88, c_70, c_10953, c_11214])).
% 12.13/4.50  tff(c_11224, plain, (k2_lattices('#skF_5', '#skF_7', '#skF_6')='#skF_6' | ~r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', '#skF_7', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_78, c_11223])).
% 12.13/4.50  tff(c_11231, plain, (~r1_lattices('#skF_5', '#skF_6', k2_lattices('#skF_5', '#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_11224])).
% 12.13/4.50  tff(c_11234, plain, (~r1_lattices('#skF_5', '#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_8451, c_11231])).
% 12.13/4.50  tff(c_11238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5024, c_11234])).
% 12.13/4.50  tff(c_11239, plain, (k2_lattices('#skF_5', '#skF_7', '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_11224])).
% 12.13/4.50  tff(c_6823, plain, (![A_351, B_352, C_353]: (k4_lattices(A_351, B_352, C_353)=k2_lattices(A_351, B_352, C_353) | ~m1_subset_1(C_353, u1_struct_0(A_351)) | ~m1_subset_1(B_352, u1_struct_0(A_351)) | ~l1_lattices(A_351) | ~v6_lattices(A_351) | v2_struct_0(A_351))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.13/4.50  tff(c_6839, plain, (![B_352]: (k4_lattices('#skF_5', B_352, '#skF_6')=k2_lattices('#skF_5', B_352, '#skF_6') | ~m1_subset_1(B_352, u1_struct_0('#skF_5')) | ~l1_lattices('#skF_5') | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_6823])).
% 12.13/4.50  tff(c_6852, plain, (![B_352]: (k4_lattices('#skF_5', B_352, '#skF_6')=k2_lattices('#skF_5', B_352, '#skF_6') | ~m1_subset_1(B_352, u1_struct_0('#skF_5')) | ~v6_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_6839])).
% 12.13/4.50  tff(c_6853, plain, (![B_352]: (k4_lattices('#skF_5', B_352, '#skF_6')=k2_lattices('#skF_5', B_352, '#skF_6') | ~m1_subset_1(B_352, u1_struct_0('#skF_5')) | ~v6_lattices('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_6852])).
% 12.13/4.50  tff(c_6931, plain, (~v6_lattices('#skF_5')), inference(splitLeft, [status(thm)], [c_6853])).
% 12.13/4.50  tff(c_6934, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_8, c_6931])).
% 12.13/4.50  tff(c_6937, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_6934])).
% 12.13/4.50  tff(c_6939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6937])).
% 12.13/4.50  tff(c_6942, plain, (![B_355]: (k4_lattices('#skF_5', B_355, '#skF_6')=k2_lattices('#skF_5', B_355, '#skF_6') | ~m1_subset_1(B_355, u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_6853])).
% 12.13/4.50  tff(c_6997, plain, (k4_lattices('#skF_5', '#skF_7', '#skF_6')=k2_lattices('#skF_5', '#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_6942])).
% 12.13/4.50  tff(c_11251, plain, (k4_lattices('#skF_5', '#skF_7', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_11239, c_6997])).
% 12.13/4.50  tff(c_74, plain, (v17_lattices('#skF_5')), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_38, plain, (![A_34, B_35]: (m1_subset_1(k7_lattices(A_34, B_35), u1_struct_0(A_34)) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_112])).
% 12.13/4.50  tff(c_6941, plain, (v6_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_6853])).
% 12.13/4.50  tff(c_7837, plain, (![A_382, B_383, C_384]: (r3_lattices(A_382, B_383, C_384) | ~r1_lattices(A_382, B_383, C_384) | ~m1_subset_1(C_384, u1_struct_0(A_382)) | ~m1_subset_1(B_383, u1_struct_0(A_382)) | ~l3_lattices(A_382) | ~v9_lattices(A_382) | ~v8_lattices(A_382) | ~v6_lattices(A_382) | v2_struct_0(A_382))), inference(cnfTransformation, [status(thm)], [f_163])).
% 12.13/4.50  tff(c_14031, plain, (![A_607, B_608, B_609]: (r3_lattices(A_607, B_608, k7_lattices(A_607, B_609)) | ~r1_lattices(A_607, B_608, k7_lattices(A_607, B_609)) | ~m1_subset_1(B_608, u1_struct_0(A_607)) | ~v9_lattices(A_607) | ~v8_lattices(A_607) | ~v6_lattices(A_607) | ~m1_subset_1(B_609, u1_struct_0(A_607)) | ~l3_lattices(A_607) | v2_struct_0(A_607))), inference(resolution, [status(thm)], [c_38, c_7837])).
% 12.13/4.50  tff(c_64, plain, (~r3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_279])).
% 12.13/4.50  tff(c_14036, plain, (~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~v9_lattices('#skF_5') | ~v8_lattices('#skF_5') | ~v6_lattices('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_14031, c_64])).
% 12.13/4.50  tff(c_14040, plain, (~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_6941, c_6759, c_6757, c_14036])).
% 12.13/4.50  tff(c_14041, plain, (~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6')) | ~m1_subset_1(k7_lattices('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_78, c_14040])).
% 12.13/4.50  tff(c_14042, plain, (~m1_subset_1(k7_lattices('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_14041])).
% 12.13/4.50  tff(c_14045, plain, (~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_38, c_14042])).
% 12.13/4.50  tff(c_14048, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_14045])).
% 12.13/4.50  tff(c_14050, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_14048])).
% 12.13/4.50  tff(c_14052, plain, (m1_subset_1(k7_lattices('#skF_5', '#skF_7'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_14041])).
% 12.13/4.50  tff(c_6633, plain, (![A_34, B_344, B_35]: (k3_lattices(A_34, B_344, k7_lattices(A_34, B_35))=k1_lattices(A_34, B_344, k7_lattices(A_34, B_35)) | ~m1_subset_1(B_344, u1_struct_0(A_34)) | ~l2_lattices(A_34) | ~v4_lattices(A_34) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_38, c_6615])).
% 12.13/4.50  tff(c_14070, plain, (![B_35]: (k3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_35))=k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_35)) | ~l2_lattices('#skF_5') | ~v4_lattices('#skF_5') | ~m1_subset_1(B_35, u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_14052, c_6633])).
% 12.13/4.50  tff(c_14218, plain, (![B_35]: (k3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_35))=k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_35)) | ~m1_subset_1(B_35, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_6658, c_88, c_14070])).
% 12.13/4.50  tff(c_20221, plain, (![B_686]: (k3_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_686))=k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_686)) | ~m1_subset_1(B_686, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_14218])).
% 12.13/4.50  tff(c_62, plain, (![A_78, B_82, C_84]: (k3_lattices(A_78, k7_lattices(A_78, B_82), k7_lattices(A_78, C_84))=k7_lattices(A_78, k4_lattices(A_78, B_82, C_84)) | ~m1_subset_1(C_84, u1_struct_0(A_78)) | ~m1_subset_1(B_82, u1_struct_0(A_78)) | ~l3_lattices(A_78) | ~v17_lattices(A_78) | ~v10_lattices(A_78) | v2_struct_0(A_78))), inference(cnfTransformation, [status(thm)], [f_259])).
% 12.13/4.50  tff(c_20230, plain, (![B_686]: (k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_686))=k7_lattices('#skF_5', k4_lattices('#skF_5', '#skF_7', B_686)) | ~m1_subset_1(B_686, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | ~v17_lattices('#skF_5') | ~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1(B_686, u1_struct_0('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_20221, c_62])).
% 12.13/4.50  tff(c_20245, plain, (![B_686]: (k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_686))=k7_lattices('#skF_5', k4_lattices('#skF_5', '#skF_7', B_686)) | v2_struct_0('#skF_5') | ~m1_subset_1(B_686, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_68, c_20230])).
% 12.13/4.50  tff(c_20253, plain, (![B_687]: (k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', B_687))=k7_lattices('#skF_5', k4_lattices('#skF_5', '#skF_7', B_687)) | ~m1_subset_1(B_687, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_78, c_20245])).
% 12.13/4.50  tff(c_122, plain, (![A_34, B_112, B_35]: (r1_lattices(A_34, B_112, k7_lattices(A_34, B_35)) | k1_lattices(A_34, B_112, k7_lattices(A_34, B_35))!=k7_lattices(A_34, B_35) | ~m1_subset_1(B_112, u1_struct_0(A_34)) | ~l2_lattices(A_34) | ~m1_subset_1(B_35, u1_struct_0(A_34)) | ~l3_lattices(A_34) | v2_struct_0(A_34))), inference(resolution, [status(thm)], [c_38, c_104])).
% 12.13/4.50  tff(c_14051, plain, (~r1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_14041])).
% 12.13/4.50  tff(c_14335, plain, (k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6'))!=k7_lattices('#skF_5', '#skF_6') | ~m1_subset_1(k7_lattices('#skF_5', '#skF_7'), u1_struct_0('#skF_5')) | ~l2_lattices('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l3_lattices('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_122, c_14051])).
% 12.13/4.50  tff(c_14342, plain, (k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6'))!=k7_lattices('#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_88, c_14052, c_14335])).
% 12.13/4.50  tff(c_14343, plain, (k1_lattices('#skF_5', k7_lattices('#skF_5', '#skF_7'), k7_lattices('#skF_5', '#skF_6'))!=k7_lattices('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_14342])).
% 12.13/4.50  tff(c_20266, plain, (k7_lattices('#skF_5', k4_lattices('#skF_5', '#skF_7', '#skF_6'))!=k7_lattices('#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_20253, c_14343])).
% 12.13/4.50  tff(c_20291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_11251, c_20266])).
% 12.13/4.50  tff(c_20293, plain, (~v8_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_6701])).
% 12.13/4.50  tff(c_20327, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_4, c_20293])).
% 12.13/4.50  tff(c_20330, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_20327])).
% 12.13/4.50  tff(c_20332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_20330])).
% 12.13/4.50  tff(c_20334, plain, (~v9_lattices('#skF_5')), inference(splitRight, [status(thm)], [c_6705])).
% 12.13/4.50  tff(c_20337, plain, (~v10_lattices('#skF_5') | v2_struct_0('#skF_5') | ~l3_lattices('#skF_5')), inference(resolution, [status(thm)], [c_2, c_20334])).
% 12.13/4.50  tff(c_20340, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_76, c_20337])).
% 12.13/4.50  tff(c_20342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_20340])).
% 12.13/4.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.13/4.50  
% 12.13/4.50  Inference rules
% 12.13/4.50  ----------------------
% 12.13/4.50  #Ref     : 0
% 12.13/4.50  #Sup     : 3814
% 12.13/4.50  #Fact    : 0
% 12.13/4.50  #Define  : 0
% 12.13/4.50  #Split   : 117
% 12.13/4.50  #Chain   : 0
% 12.13/4.50  #Close   : 0
% 12.13/4.50  
% 12.13/4.50  Ordering : KBO
% 12.13/4.50  
% 12.13/4.50  Simplification rules
% 12.13/4.50  ----------------------
% 12.13/4.50  #Subsume      : 338
% 12.13/4.50  #Demod        : 6883
% 12.13/4.50  #Tautology    : 1805
% 12.13/4.50  #SimpNegUnit  : 1688
% 12.13/4.50  #BackRed      : 21
% 12.13/4.50  
% 12.13/4.50  #Partial instantiations: 0
% 12.13/4.50  #Strategies tried      : 1
% 12.13/4.50  
% 12.13/4.50  Timing (in seconds)
% 12.13/4.50  ----------------------
% 12.13/4.50  Preprocessing        : 0.37
% 12.13/4.50  Parsing              : 0.19
% 12.13/4.50  CNF conversion       : 0.03
% 12.13/4.50  Main loop            : 3.29
% 12.13/4.50  Inferencing          : 0.96
% 12.13/4.50  Reduction            : 1.27
% 12.13/4.50  Demodulation         : 0.91
% 12.13/4.50  BG Simplification    : 0.11
% 12.13/4.50  Subsumption          : 0.75
% 12.13/4.50  Abstraction          : 0.17
% 12.13/4.50  MUC search           : 0.00
% 12.13/4.50  Cooper               : 0.00
% 12.13/4.50  Total                : 3.74
% 12.13/4.50  Index Insertion      : 0.00
% 12.13/4.50  Index Deletion       : 0.00
% 12.13/4.50  Index Matching       : 0.00
% 12.13/4.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
