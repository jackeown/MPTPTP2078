%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:28 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 8.18s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 805 expanded)
%              Number of leaves         :   50 ( 324 expanded)
%              Depth                    :   31
%              Number of atoms          :  507 (2487 expanded)
%              Number of equality atoms :   27 ( 396 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k3_tarski(A),A)
         => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_177,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_169,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_189,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_202,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( r1_orders_2(A,B,C)
                  & r1_orders_2(A,C,B) )
               => B = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).

tff(f_185,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_131,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => m1_subset_1(k4_yellow_0(A),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_0)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k4_yellow_0(A) = k2_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_yellow_0(A,B)
           => ( C = k2_yellow_0(A,B)
            <=> ( r1_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r1_lattice3(A,B,D)
                     => r1_orders_2(A,D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

tff(f_165,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

tff(c_92,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_90,plain,(
    r2_hidden(k3_tarski('#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_127,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(A_102,B_103)
      | ~ r2_hidden(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    m1_subset_1(k3_tarski('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_127])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r1_tarski(A_2,k3_tarski(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_81] : v3_orders_2(k2_yellow_1(A_81)) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_66,plain,(
    ! [A_80] : l1_orders_2(k2_yellow_1(A_80)) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_80,plain,(
    ! [A_83] : u1_struct_0(k2_yellow_1(A_83)) = A_83 ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_84,plain,(
    ! [A_84,B_88,C_90] :
      ( r3_orders_2(k2_yellow_1(A_84),B_88,C_90)
      | ~ r1_tarski(B_88,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(k2_yellow_1(A_84)))
      | ~ m1_subset_1(B_88,u1_struct_0(k2_yellow_1(A_84)))
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_94,plain,(
    ! [A_84,B_88,C_90] :
      ( r3_orders_2(k2_yellow_1(A_84),B_88,C_90)
      | ~ r1_tarski(B_88,C_90)
      | ~ m1_subset_1(C_90,A_84)
      | ~ m1_subset_1(B_88,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_84])).

tff(c_425,plain,(
    ! [A_205,B_206,C_207] :
      ( r1_orders_2(A_205,B_206,C_207)
      | ~ r3_orders_2(A_205,B_206,C_207)
      | ~ m1_subset_1(C_207,u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205)
      | ~ v3_orders_2(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_427,plain,(
    ! [A_84,B_88,C_90] :
      ( r1_orders_2(k2_yellow_1(A_84),B_88,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(k2_yellow_1(A_84)))
      | ~ m1_subset_1(B_88,u1_struct_0(k2_yellow_1(A_84)))
      | ~ l1_orders_2(k2_yellow_1(A_84))
      | ~ v3_orders_2(k2_yellow_1(A_84))
      | v2_struct_0(k2_yellow_1(A_84))
      | ~ r1_tarski(B_88,C_90)
      | ~ m1_subset_1(C_90,A_84)
      | ~ m1_subset_1(B_88,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_94,c_425])).

tff(c_430,plain,(
    ! [A_84,B_88,C_90] :
      ( r1_orders_2(k2_yellow_1(A_84),B_88,C_90)
      | v2_struct_0(k2_yellow_1(A_84))
      | ~ r1_tarski(B_88,C_90)
      | ~ m1_subset_1(C_90,A_84)
      | ~ m1_subset_1(B_88,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_80,c_80,c_427])).

tff(c_74,plain,(
    ! [A_81] : v5_orders_2(k2_yellow_1(A_81)) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_553,plain,(
    ! [C_277,B_278,A_279] :
      ( C_277 = B_278
      | ~ r1_orders_2(A_279,C_277,B_278)
      | ~ r1_orders_2(A_279,B_278,C_277)
      | ~ m1_subset_1(C_277,u1_struct_0(A_279))
      | ~ m1_subset_1(B_278,u1_struct_0(A_279))
      | ~ l1_orders_2(A_279)
      | ~ v5_orders_2(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_555,plain,(
    ! [C_90,B_88,A_84] :
      ( C_90 = B_88
      | ~ r1_orders_2(k2_yellow_1(A_84),C_90,B_88)
      | ~ m1_subset_1(B_88,u1_struct_0(k2_yellow_1(A_84)))
      | ~ m1_subset_1(C_90,u1_struct_0(k2_yellow_1(A_84)))
      | ~ l1_orders_2(k2_yellow_1(A_84))
      | ~ v5_orders_2(k2_yellow_1(A_84))
      | v2_struct_0(k2_yellow_1(A_84))
      | ~ r1_tarski(B_88,C_90)
      | ~ m1_subset_1(C_90,A_84)
      | ~ m1_subset_1(B_88,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(resolution,[status(thm)],[c_430,c_553])).

tff(c_569,plain,(
    ! [C_280,B_281,A_282] :
      ( C_280 = B_281
      | ~ r1_orders_2(k2_yellow_1(A_282),C_280,B_281)
      | v2_struct_0(k2_yellow_1(A_282))
      | ~ r1_tarski(B_281,C_280)
      | ~ m1_subset_1(C_280,A_282)
      | ~ m1_subset_1(B_281,A_282)
      | v1_xboole_0(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_80,c_80,c_555])).

tff(c_582,plain,(
    ! [C_283,B_284,A_285] :
      ( C_283 = B_284
      | ~ r1_tarski(C_283,B_284)
      | v2_struct_0(k2_yellow_1(A_285))
      | ~ r1_tarski(B_284,C_283)
      | ~ m1_subset_1(C_283,A_285)
      | ~ m1_subset_1(B_284,A_285)
      | v1_xboole_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_430,c_569])).

tff(c_758,plain,(
    ! [B_325,A_326,A_327] :
      ( k3_tarski(B_325) = A_326
      | v2_struct_0(k2_yellow_1(A_327))
      | ~ r1_tarski(k3_tarski(B_325),A_326)
      | ~ m1_subset_1(A_326,A_327)
      | ~ m1_subset_1(k3_tarski(B_325),A_327)
      | v1_xboole_0(A_327)
      | ~ r2_hidden(A_326,B_325) ) ),
    inference(resolution,[status(thm)],[c_4,c_582])).

tff(c_1754,plain,(
    ! [B_414,B_413,A_415] :
      ( k3_tarski(B_414) = k3_tarski(B_413)
      | v2_struct_0(k2_yellow_1(A_415))
      | ~ m1_subset_1(k3_tarski(B_414),A_415)
      | ~ m1_subset_1(k3_tarski(B_413),A_415)
      | v1_xboole_0(A_415)
      | ~ r2_hidden(k3_tarski(B_414),B_413)
      | ~ r2_hidden(k3_tarski(B_413),B_414) ) ),
    inference(resolution,[status(thm)],[c_4,c_758])).

tff(c_1756,plain,(
    ! [B_413] :
      ( k3_tarski(B_413) = k3_tarski('#skF_5')
      | v2_struct_0(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1(k3_tarski(B_413),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ r2_hidden(k3_tarski('#skF_5'),B_413)
      | ~ r2_hidden(k3_tarski(B_413),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_131,c_1754])).

tff(c_1759,plain,(
    ! [B_413] :
      ( k3_tarski(B_413) = k3_tarski('#skF_5')
      | v2_struct_0(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1(k3_tarski(B_413),'#skF_5')
      | ~ r2_hidden(k3_tarski('#skF_5'),B_413)
      | ~ r2_hidden(k3_tarski(B_413),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1756])).

tff(c_1760,plain,(
    v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1759])).

tff(c_78,plain,(
    ! [A_82] :
      ( ~ v2_struct_0(k2_yellow_1(A_82))
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_1763,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1760,c_78])).

tff(c_1767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1763])).

tff(c_1769,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1759])).

tff(c_88,plain,(
    k4_yellow_0(k2_yellow_1('#skF_5')) != k3_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_132,plain,(
    ! [A_104] :
      ( m1_subset_1(k4_yellow_0(A_104),u1_struct_0(A_104))
      | ~ l1_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_135,plain,(
    ! [A_83] :
      ( m1_subset_1(k4_yellow_0(k2_yellow_1(A_83)),A_83)
      | ~ l1_orders_2(k2_yellow_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_132])).

tff(c_137,plain,(
    ! [A_83] : m1_subset_1(k4_yellow_0(k2_yellow_1(A_83)),A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_135])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_118,B_119,C_120] :
      ( r2_hidden('#skF_1'(A_118,B_119,C_120),B_119)
      | r1_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_267,plain,(
    ! [B_148,A_149,C_150] :
      ( ~ r1_tarski(B_148,'#skF_1'(A_149,B_148,C_150))
      | r1_lattice3(A_149,B_148,C_150)
      | ~ m1_subset_1(C_150,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149) ) ),
    inference(resolution,[status(thm)],[c_191,c_10])).

tff(c_273,plain,(
    ! [A_151,C_152] :
      ( r1_lattice3(A_151,k1_xboole_0,C_152)
      | ~ m1_subset_1(C_152,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151) ) ),
    inference(resolution,[status(thm)],[c_2,c_267])).

tff(c_290,plain,(
    ! [A_83,C_152] :
      ( r1_lattice3(k2_yellow_1(A_83),k1_xboole_0,C_152)
      | ~ m1_subset_1(C_152,A_83)
      | ~ l1_orders_2(k2_yellow_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_273])).

tff(c_296,plain,(
    ! [A_83,C_152] :
      ( r1_lattice3(k2_yellow_1(A_83),k1_xboole_0,C_152)
      | ~ m1_subset_1(C_152,A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_290])).

tff(c_30,plain,(
    ! [A_32,B_39,C_40] :
      ( r2_hidden('#skF_2'(A_32,B_39,C_40),B_39)
      | r2_lattice3(A_32,B_39,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_206,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_2'(A_123,B_124,C_125),B_124)
      | r2_lattice3(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_213,plain,(
    ! [A_123,B_124,C_125] :
      ( m1_subset_1('#skF_2'(A_123,B_124,C_125),B_124)
      | r2_lattice3(A_123,B_124,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_123))
      | ~ l1_orders_2(A_123) ) ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_431,plain,(
    ! [A_208,B_209,C_210] :
      ( r1_orders_2(k2_yellow_1(A_208),B_209,C_210)
      | v2_struct_0(k2_yellow_1(A_208))
      | ~ r1_tarski(B_209,C_210)
      | ~ m1_subset_1(C_210,A_208)
      | ~ m1_subset_1(B_209,A_208)
      | v1_xboole_0(A_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_80,c_80,c_427])).

tff(c_28,plain,(
    ! [A_32,B_39,C_40] :
      ( ~ r1_orders_2(A_32,'#skF_2'(A_32,B_39,C_40),C_40)
      | r2_lattice3(A_32,B_39,C_40)
      | ~ m1_subset_1(C_40,u1_struct_0(A_32))
      | ~ l1_orders_2(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_439,plain,(
    ! [A_208,B_39,C_210] :
      ( r2_lattice3(k2_yellow_1(A_208),B_39,C_210)
      | ~ m1_subset_1(C_210,u1_struct_0(k2_yellow_1(A_208)))
      | ~ l1_orders_2(k2_yellow_1(A_208))
      | v2_struct_0(k2_yellow_1(A_208))
      | ~ r1_tarski('#skF_2'(k2_yellow_1(A_208),B_39,C_210),C_210)
      | ~ m1_subset_1(C_210,A_208)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_208),B_39,C_210),A_208)
      | v1_xboole_0(A_208) ) ),
    inference(resolution,[status(thm)],[c_431,c_28])).

tff(c_1946,plain,(
    ! [A_445,B_446,C_447] :
      ( r2_lattice3(k2_yellow_1(A_445),B_446,C_447)
      | v2_struct_0(k2_yellow_1(A_445))
      | ~ r1_tarski('#skF_2'(k2_yellow_1(A_445),B_446,C_447),C_447)
      | ~ m1_subset_1(C_447,A_445)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_445),B_446,C_447),A_445)
      | v1_xboole_0(A_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80,c_439])).

tff(c_4217,plain,(
    ! [A_691,B_692,B_693] :
      ( r2_lattice3(k2_yellow_1(A_691),B_692,k3_tarski(B_693))
      | v2_struct_0(k2_yellow_1(A_691))
      | ~ m1_subset_1(k3_tarski(B_693),A_691)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_691),B_692,k3_tarski(B_693)),A_691)
      | v1_xboole_0(A_691)
      | ~ r2_hidden('#skF_2'(k2_yellow_1(A_691),B_692,k3_tarski(B_693)),B_693) ) ),
    inference(resolution,[status(thm)],[c_4,c_1946])).

tff(c_4220,plain,(
    ! [B_124,B_693] :
      ( v2_struct_0(k2_yellow_1(B_124))
      | ~ m1_subset_1(k3_tarski(B_693),B_124)
      | v1_xboole_0(B_124)
      | ~ r2_hidden('#skF_2'(k2_yellow_1(B_124),B_124,k3_tarski(B_693)),B_693)
      | r2_lattice3(k2_yellow_1(B_124),B_124,k3_tarski(B_693))
      | ~ m1_subset_1(k3_tarski(B_693),u1_struct_0(k2_yellow_1(B_124)))
      | ~ l1_orders_2(k2_yellow_1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_213,c_4217])).

tff(c_4228,plain,(
    ! [B_694,B_695] :
      ( v2_struct_0(k2_yellow_1(B_694))
      | v1_xboole_0(B_694)
      | ~ r2_hidden('#skF_2'(k2_yellow_1(B_694),B_694,k3_tarski(B_695)),B_695)
      | r2_lattice3(k2_yellow_1(B_694),B_694,k3_tarski(B_695))
      | ~ m1_subset_1(k3_tarski(B_695),B_694) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80,c_4220])).

tff(c_4232,plain,(
    ! [B_39] :
      ( v2_struct_0(k2_yellow_1(B_39))
      | v1_xboole_0(B_39)
      | ~ m1_subset_1(k3_tarski(B_39),B_39)
      | r2_lattice3(k2_yellow_1(B_39),B_39,k3_tarski(B_39))
      | ~ m1_subset_1(k3_tarski(B_39),u1_struct_0(k2_yellow_1(B_39)))
      | ~ l1_orders_2(k2_yellow_1(B_39)) ) ),
    inference(resolution,[status(thm)],[c_30,c_4228])).

tff(c_4241,plain,(
    ! [B_696] :
      ( v2_struct_0(k2_yellow_1(B_696))
      | v1_xboole_0(B_696)
      | r2_lattice3(k2_yellow_1(B_696),B_696,k3_tarski(B_696))
      | ~ m1_subset_1(k3_tarski(B_696),B_696) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80,c_4232])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_399,plain,(
    ! [A_197,D_198,C_199,B_200] :
      ( r1_orders_2(A_197,D_198,C_199)
      | ~ r2_hidden(D_198,B_200)
      | ~ m1_subset_1(D_198,u1_struct_0(A_197))
      | ~ r2_lattice3(A_197,B_200,C_199)
      | ~ m1_subset_1(C_199,u1_struct_0(A_197))
      | ~ l1_orders_2(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_827,plain,(
    ! [A_340,A_341,C_342,B_343] :
      ( r1_orders_2(A_340,A_341,C_342)
      | ~ m1_subset_1(A_341,u1_struct_0(A_340))
      | ~ r2_lattice3(A_340,B_343,C_342)
      | ~ m1_subset_1(C_342,u1_struct_0(A_340))
      | ~ l1_orders_2(A_340)
      | v1_xboole_0(B_343)
      | ~ m1_subset_1(A_341,B_343) ) ),
    inference(resolution,[status(thm)],[c_8,c_399])).

tff(c_862,plain,(
    ! [A_83,A_341,C_342,B_343] :
      ( r1_orders_2(k2_yellow_1(A_83),A_341,C_342)
      | ~ m1_subset_1(A_341,A_83)
      | ~ r2_lattice3(k2_yellow_1(A_83),B_343,C_342)
      | ~ m1_subset_1(C_342,u1_struct_0(k2_yellow_1(A_83)))
      | ~ l1_orders_2(k2_yellow_1(A_83))
      | v1_xboole_0(B_343)
      | ~ m1_subset_1(A_341,B_343) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_827])).

tff(c_877,plain,(
    ! [A_83,A_341,C_342,B_343] :
      ( r1_orders_2(k2_yellow_1(A_83),A_341,C_342)
      | ~ m1_subset_1(A_341,A_83)
      | ~ r2_lattice3(k2_yellow_1(A_83),B_343,C_342)
      | ~ m1_subset_1(C_342,A_83)
      | v1_xboole_0(B_343)
      | ~ m1_subset_1(A_341,B_343) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80,c_862])).

tff(c_4407,plain,(
    ! [B_707,A_708] :
      ( r1_orders_2(k2_yellow_1(B_707),A_708,k3_tarski(B_707))
      | ~ m1_subset_1(A_708,B_707)
      | v2_struct_0(k2_yellow_1(B_707))
      | v1_xboole_0(B_707)
      | ~ m1_subset_1(k3_tarski(B_707),B_707) ) ),
    inference(resolution,[status(thm)],[c_4241,c_877])).

tff(c_611,plain,(
    ! [A_290,B_291,C_292] :
      ( r3_orders_2(A_290,B_291,C_292)
      | ~ r1_orders_2(A_290,B_291,C_292)
      | ~ m1_subset_1(C_292,u1_struct_0(A_290))
      | ~ m1_subset_1(B_291,u1_struct_0(A_290))
      | ~ l1_orders_2(A_290)
      | ~ v3_orders_2(A_290)
      | v2_struct_0(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_639,plain,(
    ! [A_83,B_291,C_292] :
      ( r3_orders_2(k2_yellow_1(A_83),B_291,C_292)
      | ~ r1_orders_2(k2_yellow_1(A_83),B_291,C_292)
      | ~ m1_subset_1(C_292,A_83)
      | ~ m1_subset_1(B_291,u1_struct_0(k2_yellow_1(A_83)))
      | ~ l1_orders_2(k2_yellow_1(A_83))
      | ~ v3_orders_2(k2_yellow_1(A_83))
      | v2_struct_0(k2_yellow_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_611])).

tff(c_652,plain,(
    ! [A_293,B_294,C_295] :
      ( r3_orders_2(k2_yellow_1(A_293),B_294,C_295)
      | ~ r1_orders_2(k2_yellow_1(A_293),B_294,C_295)
      | ~ m1_subset_1(C_295,A_293)
      | ~ m1_subset_1(B_294,A_293)
      | v2_struct_0(k2_yellow_1(A_293)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_80,c_639])).

tff(c_86,plain,(
    ! [B_88,C_90,A_84] :
      ( r1_tarski(B_88,C_90)
      | ~ r3_orders_2(k2_yellow_1(A_84),B_88,C_90)
      | ~ m1_subset_1(C_90,u1_struct_0(k2_yellow_1(A_84)))
      | ~ m1_subset_1(B_88,u1_struct_0(k2_yellow_1(A_84)))
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_93,plain,(
    ! [B_88,C_90,A_84] :
      ( r1_tarski(B_88,C_90)
      | ~ r3_orders_2(k2_yellow_1(A_84),B_88,C_90)
      | ~ m1_subset_1(C_90,A_84)
      | ~ m1_subset_1(B_88,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_80,c_86])).

tff(c_661,plain,(
    ! [B_294,C_295,A_293] :
      ( r1_tarski(B_294,C_295)
      | v1_xboole_0(A_293)
      | ~ r1_orders_2(k2_yellow_1(A_293),B_294,C_295)
      | ~ m1_subset_1(C_295,A_293)
      | ~ m1_subset_1(B_294,A_293)
      | v2_struct_0(k2_yellow_1(A_293)) ) ),
    inference(resolution,[status(thm)],[c_652,c_93])).

tff(c_4484,plain,(
    ! [A_710,B_711] :
      ( r1_tarski(A_710,k3_tarski(B_711))
      | ~ m1_subset_1(A_710,B_711)
      | v2_struct_0(k2_yellow_1(B_711))
      | v1_xboole_0(B_711)
      | ~ m1_subset_1(k3_tarski(B_711),B_711) ) ),
    inference(resolution,[status(thm)],[c_4407,c_661])).

tff(c_4486,plain,(
    ! [A_710] :
      ( r1_tarski(A_710,k3_tarski('#skF_5'))
      | ~ m1_subset_1(A_710,'#skF_5')
      | v2_struct_0(k2_yellow_1('#skF_5'))
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_131,c_4484])).

tff(c_4523,plain,(
    ! [A_717] :
      ( r1_tarski(A_717,k3_tarski('#skF_5'))
      | ~ m1_subset_1(A_717,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1769,c_4486])).

tff(c_139,plain,(
    ! [A_106] :
      ( k2_yellow_0(A_106,k1_xboole_0) = k4_yellow_0(A_106)
      | ~ l1_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_143,plain,(
    ! [A_80] : k2_yellow_0(k2_yellow_1(A_80),k1_xboole_0) = k4_yellow_0(k2_yellow_1(A_80)) ),
    inference(resolution,[status(thm)],[c_66,c_139])).

tff(c_1408,plain,(
    ! [A_390,D_391,B_392] :
      ( r1_orders_2(A_390,D_391,k2_yellow_0(A_390,B_392))
      | ~ r1_lattice3(A_390,B_392,D_391)
      | ~ m1_subset_1(D_391,u1_struct_0(A_390))
      | ~ r2_yellow_0(A_390,B_392)
      | ~ m1_subset_1(k2_yellow_0(A_390,B_392),u1_struct_0(A_390))
      | ~ l1_orders_2(A_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1410,plain,(
    ! [A_80,D_391] :
      ( r1_orders_2(k2_yellow_1(A_80),D_391,k2_yellow_0(k2_yellow_1(A_80),k1_xboole_0))
      | ~ r1_lattice3(k2_yellow_1(A_80),k1_xboole_0,D_391)
      | ~ m1_subset_1(D_391,u1_struct_0(k2_yellow_1(A_80)))
      | ~ r2_yellow_0(k2_yellow_1(A_80),k1_xboole_0)
      | ~ m1_subset_1(k4_yellow_0(k2_yellow_1(A_80)),u1_struct_0(k2_yellow_1(A_80)))
      | ~ l1_orders_2(k2_yellow_1(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_1408])).

tff(c_1417,plain,(
    ! [A_393,D_394] :
      ( r1_orders_2(k2_yellow_1(A_393),D_394,k4_yellow_0(k2_yellow_1(A_393)))
      | ~ r1_lattice3(k2_yellow_1(A_393),k1_xboole_0,D_394)
      | ~ m1_subset_1(D_394,A_393)
      | ~ r2_yellow_0(k2_yellow_1(A_393),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_137,c_80,c_80,c_143,c_1410])).

tff(c_562,plain,(
    ! [C_90,B_88,A_84] :
      ( C_90 = B_88
      | ~ r1_orders_2(k2_yellow_1(A_84),C_90,B_88)
      | v2_struct_0(k2_yellow_1(A_84))
      | ~ r1_tarski(B_88,C_90)
      | ~ m1_subset_1(C_90,A_84)
      | ~ m1_subset_1(B_88,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_80,c_80,c_555])).

tff(c_1438,plain,(
    ! [A_393,D_394] :
      ( k4_yellow_0(k2_yellow_1(A_393)) = D_394
      | v2_struct_0(k2_yellow_1(A_393))
      | ~ r1_tarski(k4_yellow_0(k2_yellow_1(A_393)),D_394)
      | ~ m1_subset_1(k4_yellow_0(k2_yellow_1(A_393)),A_393)
      | v1_xboole_0(A_393)
      | ~ r1_lattice3(k2_yellow_1(A_393),k1_xboole_0,D_394)
      | ~ m1_subset_1(D_394,A_393)
      | ~ r2_yellow_0(k2_yellow_1(A_393),k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1417,c_562])).

tff(c_1464,plain,(
    ! [A_393,D_394] :
      ( k4_yellow_0(k2_yellow_1(A_393)) = D_394
      | v2_struct_0(k2_yellow_1(A_393))
      | ~ r1_tarski(k4_yellow_0(k2_yellow_1(A_393)),D_394)
      | v1_xboole_0(A_393)
      | ~ r1_lattice3(k2_yellow_1(A_393),k1_xboole_0,D_394)
      | ~ m1_subset_1(D_394,A_393)
      | ~ r2_yellow_0(k2_yellow_1(A_393),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_1438])).

tff(c_5042,plain,(
    ! [A_757] :
      ( k4_yellow_0(k2_yellow_1(A_757)) = k3_tarski('#skF_5')
      | v2_struct_0(k2_yellow_1(A_757))
      | v1_xboole_0(A_757)
      | ~ r1_lattice3(k2_yellow_1(A_757),k1_xboole_0,k3_tarski('#skF_5'))
      | ~ m1_subset_1(k3_tarski('#skF_5'),A_757)
      | ~ r2_yellow_0(k2_yellow_1(A_757),k1_xboole_0)
      | ~ m1_subset_1(k4_yellow_0(k2_yellow_1(A_757)),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4523,c_1464])).

tff(c_5161,plain,(
    ! [A_768] :
      ( k4_yellow_0(k2_yellow_1(A_768)) = k3_tarski('#skF_5')
      | v2_struct_0(k2_yellow_1(A_768))
      | v1_xboole_0(A_768)
      | ~ r2_yellow_0(k2_yellow_1(A_768),k1_xboole_0)
      | ~ m1_subset_1(k4_yellow_0(k2_yellow_1(A_768)),'#skF_5')
      | ~ m1_subset_1(k3_tarski('#skF_5'),A_768) ) ),
    inference(resolution,[status(thm)],[c_296,c_5042])).

tff(c_5165,plain,
    ( k4_yellow_0(k2_yellow_1('#skF_5')) = k3_tarski('#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ r2_yellow_0(k2_yellow_1('#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_137,c_5161])).

tff(c_5168,plain,
    ( k4_yellow_0(k2_yellow_1('#skF_5')) = k3_tarski('#skF_5')
    | v2_struct_0(k2_yellow_1('#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ r2_yellow_0(k2_yellow_1('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_5165])).

tff(c_5169,plain,(
    ~ r2_yellow_0(k2_yellow_1('#skF_5'),k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1769,c_88,c_5168])).

tff(c_518,plain,(
    ! [A_263,B_264,C_265] :
      ( m1_subset_1('#skF_4'(A_263,B_264,C_265),u1_struct_0(A_263))
      | r2_yellow_0(A_263,C_265)
      | ~ r1_lattice3(A_263,C_265,B_264)
      | ~ m1_subset_1(B_264,u1_struct_0(A_263))
      | ~ l1_orders_2(A_263)
      | ~ v5_orders_2(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_527,plain,(
    ! [A_83,B_264,C_265] :
      ( m1_subset_1('#skF_4'(k2_yellow_1(A_83),B_264,C_265),A_83)
      | r2_yellow_0(k2_yellow_1(A_83),C_265)
      | ~ r1_lattice3(k2_yellow_1(A_83),C_265,B_264)
      | ~ m1_subset_1(B_264,u1_struct_0(k2_yellow_1(A_83)))
      | ~ l1_orders_2(k2_yellow_1(A_83))
      | ~ v5_orders_2(k2_yellow_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_518])).

tff(c_531,plain,(
    ! [A_83,B_264,C_265] :
      ( m1_subset_1('#skF_4'(k2_yellow_1(A_83),B_264,C_265),A_83)
      | r2_yellow_0(k2_yellow_1(A_83),C_265)
      | ~ r1_lattice3(k2_yellow_1(A_83),C_265,B_264)
      | ~ m1_subset_1(B_264,A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_80,c_527])).

tff(c_445,plain,(
    ! [A_208,B_39,C_210] :
      ( r2_lattice3(k2_yellow_1(A_208),B_39,C_210)
      | v2_struct_0(k2_yellow_1(A_208))
      | ~ r1_tarski('#skF_2'(k2_yellow_1(A_208),B_39,C_210),C_210)
      | ~ m1_subset_1(C_210,A_208)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_208),B_39,C_210),A_208)
      | v1_xboole_0(A_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80,c_439])).

tff(c_5495,plain,(
    ! [A_792,B_793] :
      ( r2_lattice3(k2_yellow_1(A_792),B_793,k3_tarski('#skF_5'))
      | v2_struct_0(k2_yellow_1(A_792))
      | ~ m1_subset_1(k3_tarski('#skF_5'),A_792)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_792),B_793,k3_tarski('#skF_5')),A_792)
      | v1_xboole_0(A_792)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_792),B_793,k3_tarski('#skF_5')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4523,c_445])).

tff(c_5498,plain,(
    ! [B_124] :
      ( v2_struct_0(k2_yellow_1(B_124))
      | ~ m1_subset_1(k3_tarski('#skF_5'),B_124)
      | v1_xboole_0(B_124)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(B_124),B_124,k3_tarski('#skF_5')),'#skF_5')
      | r2_lattice3(k2_yellow_1(B_124),B_124,k3_tarski('#skF_5'))
      | ~ m1_subset_1(k3_tarski('#skF_5'),u1_struct_0(k2_yellow_1(B_124)))
      | ~ l1_orders_2(k2_yellow_1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_213,c_5495])).

tff(c_5506,plain,(
    ! [B_794] :
      ( v2_struct_0(k2_yellow_1(B_794))
      | v1_xboole_0(B_794)
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(B_794),B_794,k3_tarski('#skF_5')),'#skF_5')
      | r2_lattice3(k2_yellow_1(B_794),B_794,k3_tarski('#skF_5'))
      | ~ m1_subset_1(k3_tarski('#skF_5'),B_794) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_80,c_5498])).

tff(c_5510,plain,
    ( v2_struct_0(k2_yellow_1('#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k3_tarski('#skF_5'),'#skF_5')
    | r2_lattice3(k2_yellow_1('#skF_5'),'#skF_5',k3_tarski('#skF_5'))
    | ~ m1_subset_1(k3_tarski('#skF_5'),u1_struct_0(k2_yellow_1('#skF_5')))
    | ~ l1_orders_2(k2_yellow_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_213,c_5506])).

tff(c_5517,plain,
    ( v2_struct_0(k2_yellow_1('#skF_5'))
    | v1_xboole_0('#skF_5')
    | r2_lattice3(k2_yellow_1('#skF_5'),'#skF_5',k3_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_131,c_80,c_131,c_5510])).

tff(c_5518,plain,(
    r2_lattice3(k2_yellow_1('#skF_5'),'#skF_5',k3_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1769,c_5517])).

tff(c_5534,plain,(
    ! [A_341] :
      ( r1_orders_2(k2_yellow_1('#skF_5'),A_341,k3_tarski('#skF_5'))
      | ~ m1_subset_1(k3_tarski('#skF_5'),'#skF_5')
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_341,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5518,c_877])).

tff(c_5565,plain,(
    ! [A_341] :
      ( r1_orders_2(k2_yellow_1('#skF_5'),A_341,k3_tarski('#skF_5'))
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_341,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_5534])).

tff(c_5772,plain,(
    ! [A_800] :
      ( r1_orders_2(k2_yellow_1('#skF_5'),A_800,k3_tarski('#skF_5'))
      | ~ m1_subset_1(A_800,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_5565])).

tff(c_52,plain,(
    ! [A_58,B_70,C_76] :
      ( ~ r1_orders_2(A_58,'#skF_4'(A_58,B_70,C_76),B_70)
      | r2_yellow_0(A_58,C_76)
      | ~ r1_lattice3(A_58,C_76,B_70)
      | ~ m1_subset_1(B_70,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | ~ v5_orders_2(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_5815,plain,(
    ! [C_76] :
      ( r2_yellow_0(k2_yellow_1('#skF_5'),C_76)
      | ~ r1_lattice3(k2_yellow_1('#skF_5'),C_76,k3_tarski('#skF_5'))
      | ~ m1_subset_1(k3_tarski('#skF_5'),u1_struct_0(k2_yellow_1('#skF_5')))
      | ~ l1_orders_2(k2_yellow_1('#skF_5'))
      | ~ v5_orders_2(k2_yellow_1('#skF_5'))
      | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5'),k3_tarski('#skF_5'),C_76),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5772,c_52])).

tff(c_6243,plain,(
    ! [C_810] :
      ( r2_yellow_0(k2_yellow_1('#skF_5'),C_810)
      | ~ r1_lattice3(k2_yellow_1('#skF_5'),C_810,k3_tarski('#skF_5'))
      | ~ m1_subset_1('#skF_4'(k2_yellow_1('#skF_5'),k3_tarski('#skF_5'),C_810),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_66,c_131,c_80,c_5815])).

tff(c_6251,plain,(
    ! [C_265] :
      ( r2_yellow_0(k2_yellow_1('#skF_5'),C_265)
      | ~ r1_lattice3(k2_yellow_1('#skF_5'),C_265,k3_tarski('#skF_5'))
      | ~ m1_subset_1(k3_tarski('#skF_5'),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_531,c_6243])).

tff(c_6258,plain,(
    ! [C_811] :
      ( r2_yellow_0(k2_yellow_1('#skF_5'),C_811)
      | ~ r1_lattice3(k2_yellow_1('#skF_5'),C_811,k3_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_6251])).

tff(c_6262,plain,
    ( r2_yellow_0(k2_yellow_1('#skF_5'),k1_xboole_0)
    | ~ m1_subset_1(k3_tarski('#skF_5'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_296,c_6258])).

tff(c_6265,plain,(
    r2_yellow_0(k2_yellow_1('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_6262])).

tff(c_6267,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5169,c_6265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:15:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.90  
% 8.18/2.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.90  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3
% 8.18/2.90  
% 8.18/2.90  %Foreground sorts:
% 8.18/2.90  
% 8.18/2.90  
% 8.18/2.90  %Background operators:
% 8.18/2.90  
% 8.18/2.90  
% 8.18/2.90  %Foreground operators:
% 8.18/2.90  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 8.18/2.90  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.18/2.90  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 8.18/2.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.18/2.90  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 8.18/2.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.18/2.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.18/2.90  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 8.18/2.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.18/2.90  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 8.18/2.90  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.18/2.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.18/2.90  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 8.18/2.90  tff('#skF_5', type, '#skF_5': $i).
% 8.18/2.90  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 8.18/2.90  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 8.18/2.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.18/2.90  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 8.18/2.90  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 8.18/2.90  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 8.18/2.90  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 8.18/2.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.18/2.90  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.18/2.90  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 8.18/2.90  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 8.18/2.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 8.18/2.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.18/2.90  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 8.18/2.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.18/2.90  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.18/2.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.18/2.90  
% 8.18/2.92  tff(f_210, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 8.18/2.92  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 8.18/2.92  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 8.18/2.92  tff(f_177, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 8.18/2.92  tff(f_169, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 8.18/2.92  tff(f_189, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 8.18/2.92  tff(f_202, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 8.18/2.92  tff(f_61, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 8.18/2.92  tff(f_77, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, B)) => (B = C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_orders_2)).
% 8.18/2.92  tff(f_185, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 8.18/2.92  tff(f_131, axiom, (![A]: (l1_orders_2(A) => m1_subset_1(k4_yellow_0(A), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_yellow_0)).
% 8.18/2.92  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.18/2.92  tff(f_91, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, C, D))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 8.18/2.92  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.18/2.92  tff(f_105, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 8.18/2.92  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 8.18/2.92  tff(f_127, axiom, (![A]: (l1_orders_2(A) => (k4_yellow_0(A) = k2_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_yellow_0)).
% 8.18/2.92  tff(f_123, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_yellow_0(A, B) => ((C = k2_yellow_0(A, B)) <=> (r1_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_yellow_0)).
% 8.18/2.92  tff(f_165, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C)) => (r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B)))))) & ((r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B))))) => ((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 8.18/2.92  tff(c_92, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.18/2.92  tff(c_90, plain, (r2_hidden(k3_tarski('#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.18/2.92  tff(c_127, plain, (![A_102, B_103]: (m1_subset_1(A_102, B_103) | ~r2_hidden(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.18/2.92  tff(c_131, plain, (m1_subset_1(k3_tarski('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_90, c_127])).
% 8.18/2.92  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, k3_tarski(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.18/2.92  tff(c_70, plain, (![A_81]: (v3_orders_2(k2_yellow_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.18/2.92  tff(c_66, plain, (![A_80]: (l1_orders_2(k2_yellow_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_169])).
% 8.18/2.92  tff(c_80, plain, (![A_83]: (u1_struct_0(k2_yellow_1(A_83))=A_83)), inference(cnfTransformation, [status(thm)], [f_189])).
% 8.18/2.92  tff(c_84, plain, (![A_84, B_88, C_90]: (r3_orders_2(k2_yellow_1(A_84), B_88, C_90) | ~r1_tarski(B_88, C_90) | ~m1_subset_1(C_90, u1_struct_0(k2_yellow_1(A_84))) | ~m1_subset_1(B_88, u1_struct_0(k2_yellow_1(A_84))) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.18/2.92  tff(c_94, plain, (![A_84, B_88, C_90]: (r3_orders_2(k2_yellow_1(A_84), B_88, C_90) | ~r1_tarski(B_88, C_90) | ~m1_subset_1(C_90, A_84) | ~m1_subset_1(B_88, A_84) | v1_xboole_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_84])).
% 8.18/2.92  tff(c_425, plain, (![A_205, B_206, C_207]: (r1_orders_2(A_205, B_206, C_207) | ~r3_orders_2(A_205, B_206, C_207) | ~m1_subset_1(C_207, u1_struct_0(A_205)) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | ~l1_orders_2(A_205) | ~v3_orders_2(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.18/2.92  tff(c_427, plain, (![A_84, B_88, C_90]: (r1_orders_2(k2_yellow_1(A_84), B_88, C_90) | ~m1_subset_1(C_90, u1_struct_0(k2_yellow_1(A_84))) | ~m1_subset_1(B_88, u1_struct_0(k2_yellow_1(A_84))) | ~l1_orders_2(k2_yellow_1(A_84)) | ~v3_orders_2(k2_yellow_1(A_84)) | v2_struct_0(k2_yellow_1(A_84)) | ~r1_tarski(B_88, C_90) | ~m1_subset_1(C_90, A_84) | ~m1_subset_1(B_88, A_84) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_94, c_425])).
% 8.18/2.92  tff(c_430, plain, (![A_84, B_88, C_90]: (r1_orders_2(k2_yellow_1(A_84), B_88, C_90) | v2_struct_0(k2_yellow_1(A_84)) | ~r1_tarski(B_88, C_90) | ~m1_subset_1(C_90, A_84) | ~m1_subset_1(B_88, A_84) | v1_xboole_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_80, c_80, c_427])).
% 8.18/2.92  tff(c_74, plain, (![A_81]: (v5_orders_2(k2_yellow_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.18/2.92  tff(c_553, plain, (![C_277, B_278, A_279]: (C_277=B_278 | ~r1_orders_2(A_279, C_277, B_278) | ~r1_orders_2(A_279, B_278, C_277) | ~m1_subset_1(C_277, u1_struct_0(A_279)) | ~m1_subset_1(B_278, u1_struct_0(A_279)) | ~l1_orders_2(A_279) | ~v5_orders_2(A_279))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.18/2.92  tff(c_555, plain, (![C_90, B_88, A_84]: (C_90=B_88 | ~r1_orders_2(k2_yellow_1(A_84), C_90, B_88) | ~m1_subset_1(B_88, u1_struct_0(k2_yellow_1(A_84))) | ~m1_subset_1(C_90, u1_struct_0(k2_yellow_1(A_84))) | ~l1_orders_2(k2_yellow_1(A_84)) | ~v5_orders_2(k2_yellow_1(A_84)) | v2_struct_0(k2_yellow_1(A_84)) | ~r1_tarski(B_88, C_90) | ~m1_subset_1(C_90, A_84) | ~m1_subset_1(B_88, A_84) | v1_xboole_0(A_84))), inference(resolution, [status(thm)], [c_430, c_553])).
% 8.18/2.92  tff(c_569, plain, (![C_280, B_281, A_282]: (C_280=B_281 | ~r1_orders_2(k2_yellow_1(A_282), C_280, B_281) | v2_struct_0(k2_yellow_1(A_282)) | ~r1_tarski(B_281, C_280) | ~m1_subset_1(C_280, A_282) | ~m1_subset_1(B_281, A_282) | v1_xboole_0(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_80, c_80, c_555])).
% 8.18/2.92  tff(c_582, plain, (![C_283, B_284, A_285]: (C_283=B_284 | ~r1_tarski(C_283, B_284) | v2_struct_0(k2_yellow_1(A_285)) | ~r1_tarski(B_284, C_283) | ~m1_subset_1(C_283, A_285) | ~m1_subset_1(B_284, A_285) | v1_xboole_0(A_285))), inference(resolution, [status(thm)], [c_430, c_569])).
% 8.18/2.92  tff(c_758, plain, (![B_325, A_326, A_327]: (k3_tarski(B_325)=A_326 | v2_struct_0(k2_yellow_1(A_327)) | ~r1_tarski(k3_tarski(B_325), A_326) | ~m1_subset_1(A_326, A_327) | ~m1_subset_1(k3_tarski(B_325), A_327) | v1_xboole_0(A_327) | ~r2_hidden(A_326, B_325))), inference(resolution, [status(thm)], [c_4, c_582])).
% 8.18/2.92  tff(c_1754, plain, (![B_414, B_413, A_415]: (k3_tarski(B_414)=k3_tarski(B_413) | v2_struct_0(k2_yellow_1(A_415)) | ~m1_subset_1(k3_tarski(B_414), A_415) | ~m1_subset_1(k3_tarski(B_413), A_415) | v1_xboole_0(A_415) | ~r2_hidden(k3_tarski(B_414), B_413) | ~r2_hidden(k3_tarski(B_413), B_414))), inference(resolution, [status(thm)], [c_4, c_758])).
% 8.18/2.92  tff(c_1756, plain, (![B_413]: (k3_tarski(B_413)=k3_tarski('#skF_5') | v2_struct_0(k2_yellow_1('#skF_5')) | ~m1_subset_1(k3_tarski(B_413), '#skF_5') | v1_xboole_0('#skF_5') | ~r2_hidden(k3_tarski('#skF_5'), B_413) | ~r2_hidden(k3_tarski(B_413), '#skF_5'))), inference(resolution, [status(thm)], [c_131, c_1754])).
% 8.18/2.92  tff(c_1759, plain, (![B_413]: (k3_tarski(B_413)=k3_tarski('#skF_5') | v2_struct_0(k2_yellow_1('#skF_5')) | ~m1_subset_1(k3_tarski(B_413), '#skF_5') | ~r2_hidden(k3_tarski('#skF_5'), B_413) | ~r2_hidden(k3_tarski(B_413), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_1756])).
% 8.18/2.92  tff(c_1760, plain, (v2_struct_0(k2_yellow_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_1759])).
% 8.18/2.92  tff(c_78, plain, (![A_82]: (~v2_struct_0(k2_yellow_1(A_82)) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_185])).
% 8.18/2.92  tff(c_1763, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_1760, c_78])).
% 8.18/2.92  tff(c_1767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1763])).
% 8.18/2.92  tff(c_1769, plain, (~v2_struct_0(k2_yellow_1('#skF_5'))), inference(splitRight, [status(thm)], [c_1759])).
% 8.18/2.92  tff(c_88, plain, (k4_yellow_0(k2_yellow_1('#skF_5'))!=k3_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 8.18/2.92  tff(c_132, plain, (![A_104]: (m1_subset_1(k4_yellow_0(A_104), u1_struct_0(A_104)) | ~l1_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_131])).
% 8.18/2.92  tff(c_135, plain, (![A_83]: (m1_subset_1(k4_yellow_0(k2_yellow_1(A_83)), A_83) | ~l1_orders_2(k2_yellow_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_132])).
% 8.18/2.92  tff(c_137, plain, (![A_83]: (m1_subset_1(k4_yellow_0(k2_yellow_1(A_83)), A_83))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_135])).
% 8.18/2.92  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.18/2.92  tff(c_191, plain, (![A_118, B_119, C_120]: (r2_hidden('#skF_1'(A_118, B_119, C_120), B_119) | r1_lattice3(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~l1_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.18/2.92  tff(c_10, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.18/2.92  tff(c_267, plain, (![B_148, A_149, C_150]: (~r1_tarski(B_148, '#skF_1'(A_149, B_148, C_150)) | r1_lattice3(A_149, B_148, C_150) | ~m1_subset_1(C_150, u1_struct_0(A_149)) | ~l1_orders_2(A_149))), inference(resolution, [status(thm)], [c_191, c_10])).
% 8.18/2.92  tff(c_273, plain, (![A_151, C_152]: (r1_lattice3(A_151, k1_xboole_0, C_152) | ~m1_subset_1(C_152, u1_struct_0(A_151)) | ~l1_orders_2(A_151))), inference(resolution, [status(thm)], [c_2, c_267])).
% 8.18/2.92  tff(c_290, plain, (![A_83, C_152]: (r1_lattice3(k2_yellow_1(A_83), k1_xboole_0, C_152) | ~m1_subset_1(C_152, A_83) | ~l1_orders_2(k2_yellow_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_273])).
% 8.18/2.92  tff(c_296, plain, (![A_83, C_152]: (r1_lattice3(k2_yellow_1(A_83), k1_xboole_0, C_152) | ~m1_subset_1(C_152, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_290])).
% 8.18/2.92  tff(c_30, plain, (![A_32, B_39, C_40]: (r2_hidden('#skF_2'(A_32, B_39, C_40), B_39) | r2_lattice3(A_32, B_39, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_32)) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.18/2.92  tff(c_206, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_2'(A_123, B_124, C_125), B_124) | r2_lattice3(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~l1_orders_2(A_123))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.18/2.92  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.18/2.92  tff(c_213, plain, (![A_123, B_124, C_125]: (m1_subset_1('#skF_2'(A_123, B_124, C_125), B_124) | r2_lattice3(A_123, B_124, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_123)) | ~l1_orders_2(A_123))), inference(resolution, [status(thm)], [c_206, c_6])).
% 8.18/2.92  tff(c_431, plain, (![A_208, B_209, C_210]: (r1_orders_2(k2_yellow_1(A_208), B_209, C_210) | v2_struct_0(k2_yellow_1(A_208)) | ~r1_tarski(B_209, C_210) | ~m1_subset_1(C_210, A_208) | ~m1_subset_1(B_209, A_208) | v1_xboole_0(A_208))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_80, c_80, c_427])).
% 8.18/2.92  tff(c_28, plain, (![A_32, B_39, C_40]: (~r1_orders_2(A_32, '#skF_2'(A_32, B_39, C_40), C_40) | r2_lattice3(A_32, B_39, C_40) | ~m1_subset_1(C_40, u1_struct_0(A_32)) | ~l1_orders_2(A_32))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.18/2.92  tff(c_439, plain, (![A_208, B_39, C_210]: (r2_lattice3(k2_yellow_1(A_208), B_39, C_210) | ~m1_subset_1(C_210, u1_struct_0(k2_yellow_1(A_208))) | ~l1_orders_2(k2_yellow_1(A_208)) | v2_struct_0(k2_yellow_1(A_208)) | ~r1_tarski('#skF_2'(k2_yellow_1(A_208), B_39, C_210), C_210) | ~m1_subset_1(C_210, A_208) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_208), B_39, C_210), A_208) | v1_xboole_0(A_208))), inference(resolution, [status(thm)], [c_431, c_28])).
% 8.18/2.92  tff(c_1946, plain, (![A_445, B_446, C_447]: (r2_lattice3(k2_yellow_1(A_445), B_446, C_447) | v2_struct_0(k2_yellow_1(A_445)) | ~r1_tarski('#skF_2'(k2_yellow_1(A_445), B_446, C_447), C_447) | ~m1_subset_1(C_447, A_445) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_445), B_446, C_447), A_445) | v1_xboole_0(A_445))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80, c_439])).
% 8.18/2.92  tff(c_4217, plain, (![A_691, B_692, B_693]: (r2_lattice3(k2_yellow_1(A_691), B_692, k3_tarski(B_693)) | v2_struct_0(k2_yellow_1(A_691)) | ~m1_subset_1(k3_tarski(B_693), A_691) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_691), B_692, k3_tarski(B_693)), A_691) | v1_xboole_0(A_691) | ~r2_hidden('#skF_2'(k2_yellow_1(A_691), B_692, k3_tarski(B_693)), B_693))), inference(resolution, [status(thm)], [c_4, c_1946])).
% 8.18/2.92  tff(c_4220, plain, (![B_124, B_693]: (v2_struct_0(k2_yellow_1(B_124)) | ~m1_subset_1(k3_tarski(B_693), B_124) | v1_xboole_0(B_124) | ~r2_hidden('#skF_2'(k2_yellow_1(B_124), B_124, k3_tarski(B_693)), B_693) | r2_lattice3(k2_yellow_1(B_124), B_124, k3_tarski(B_693)) | ~m1_subset_1(k3_tarski(B_693), u1_struct_0(k2_yellow_1(B_124))) | ~l1_orders_2(k2_yellow_1(B_124)))), inference(resolution, [status(thm)], [c_213, c_4217])).
% 8.18/2.92  tff(c_4228, plain, (![B_694, B_695]: (v2_struct_0(k2_yellow_1(B_694)) | v1_xboole_0(B_694) | ~r2_hidden('#skF_2'(k2_yellow_1(B_694), B_694, k3_tarski(B_695)), B_695) | r2_lattice3(k2_yellow_1(B_694), B_694, k3_tarski(B_695)) | ~m1_subset_1(k3_tarski(B_695), B_694))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80, c_4220])).
% 8.18/2.92  tff(c_4232, plain, (![B_39]: (v2_struct_0(k2_yellow_1(B_39)) | v1_xboole_0(B_39) | ~m1_subset_1(k3_tarski(B_39), B_39) | r2_lattice3(k2_yellow_1(B_39), B_39, k3_tarski(B_39)) | ~m1_subset_1(k3_tarski(B_39), u1_struct_0(k2_yellow_1(B_39))) | ~l1_orders_2(k2_yellow_1(B_39)))), inference(resolution, [status(thm)], [c_30, c_4228])).
% 8.18/2.92  tff(c_4241, plain, (![B_696]: (v2_struct_0(k2_yellow_1(B_696)) | v1_xboole_0(B_696) | r2_lattice3(k2_yellow_1(B_696), B_696, k3_tarski(B_696)) | ~m1_subset_1(k3_tarski(B_696), B_696))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80, c_4232])).
% 8.18/2.92  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.18/2.92  tff(c_399, plain, (![A_197, D_198, C_199, B_200]: (r1_orders_2(A_197, D_198, C_199) | ~r2_hidden(D_198, B_200) | ~m1_subset_1(D_198, u1_struct_0(A_197)) | ~r2_lattice3(A_197, B_200, C_199) | ~m1_subset_1(C_199, u1_struct_0(A_197)) | ~l1_orders_2(A_197))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.18/2.92  tff(c_827, plain, (![A_340, A_341, C_342, B_343]: (r1_orders_2(A_340, A_341, C_342) | ~m1_subset_1(A_341, u1_struct_0(A_340)) | ~r2_lattice3(A_340, B_343, C_342) | ~m1_subset_1(C_342, u1_struct_0(A_340)) | ~l1_orders_2(A_340) | v1_xboole_0(B_343) | ~m1_subset_1(A_341, B_343))), inference(resolution, [status(thm)], [c_8, c_399])).
% 8.18/2.92  tff(c_862, plain, (![A_83, A_341, C_342, B_343]: (r1_orders_2(k2_yellow_1(A_83), A_341, C_342) | ~m1_subset_1(A_341, A_83) | ~r2_lattice3(k2_yellow_1(A_83), B_343, C_342) | ~m1_subset_1(C_342, u1_struct_0(k2_yellow_1(A_83))) | ~l1_orders_2(k2_yellow_1(A_83)) | v1_xboole_0(B_343) | ~m1_subset_1(A_341, B_343))), inference(superposition, [status(thm), theory('equality')], [c_80, c_827])).
% 8.18/2.92  tff(c_877, plain, (![A_83, A_341, C_342, B_343]: (r1_orders_2(k2_yellow_1(A_83), A_341, C_342) | ~m1_subset_1(A_341, A_83) | ~r2_lattice3(k2_yellow_1(A_83), B_343, C_342) | ~m1_subset_1(C_342, A_83) | v1_xboole_0(B_343) | ~m1_subset_1(A_341, B_343))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80, c_862])).
% 8.18/2.92  tff(c_4407, plain, (![B_707, A_708]: (r1_orders_2(k2_yellow_1(B_707), A_708, k3_tarski(B_707)) | ~m1_subset_1(A_708, B_707) | v2_struct_0(k2_yellow_1(B_707)) | v1_xboole_0(B_707) | ~m1_subset_1(k3_tarski(B_707), B_707))), inference(resolution, [status(thm)], [c_4241, c_877])).
% 8.18/2.92  tff(c_611, plain, (![A_290, B_291, C_292]: (r3_orders_2(A_290, B_291, C_292) | ~r1_orders_2(A_290, B_291, C_292) | ~m1_subset_1(C_292, u1_struct_0(A_290)) | ~m1_subset_1(B_291, u1_struct_0(A_290)) | ~l1_orders_2(A_290) | ~v3_orders_2(A_290) | v2_struct_0(A_290))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.18/2.92  tff(c_639, plain, (![A_83, B_291, C_292]: (r3_orders_2(k2_yellow_1(A_83), B_291, C_292) | ~r1_orders_2(k2_yellow_1(A_83), B_291, C_292) | ~m1_subset_1(C_292, A_83) | ~m1_subset_1(B_291, u1_struct_0(k2_yellow_1(A_83))) | ~l1_orders_2(k2_yellow_1(A_83)) | ~v3_orders_2(k2_yellow_1(A_83)) | v2_struct_0(k2_yellow_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_611])).
% 8.18/2.92  tff(c_652, plain, (![A_293, B_294, C_295]: (r3_orders_2(k2_yellow_1(A_293), B_294, C_295) | ~r1_orders_2(k2_yellow_1(A_293), B_294, C_295) | ~m1_subset_1(C_295, A_293) | ~m1_subset_1(B_294, A_293) | v2_struct_0(k2_yellow_1(A_293)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_80, c_639])).
% 8.18/2.92  tff(c_86, plain, (![B_88, C_90, A_84]: (r1_tarski(B_88, C_90) | ~r3_orders_2(k2_yellow_1(A_84), B_88, C_90) | ~m1_subset_1(C_90, u1_struct_0(k2_yellow_1(A_84))) | ~m1_subset_1(B_88, u1_struct_0(k2_yellow_1(A_84))) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_202])).
% 8.18/2.92  tff(c_93, plain, (![B_88, C_90, A_84]: (r1_tarski(B_88, C_90) | ~r3_orders_2(k2_yellow_1(A_84), B_88, C_90) | ~m1_subset_1(C_90, A_84) | ~m1_subset_1(B_88, A_84) | v1_xboole_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_80, c_86])).
% 8.18/2.92  tff(c_661, plain, (![B_294, C_295, A_293]: (r1_tarski(B_294, C_295) | v1_xboole_0(A_293) | ~r1_orders_2(k2_yellow_1(A_293), B_294, C_295) | ~m1_subset_1(C_295, A_293) | ~m1_subset_1(B_294, A_293) | v2_struct_0(k2_yellow_1(A_293)))), inference(resolution, [status(thm)], [c_652, c_93])).
% 8.18/2.92  tff(c_4484, plain, (![A_710, B_711]: (r1_tarski(A_710, k3_tarski(B_711)) | ~m1_subset_1(A_710, B_711) | v2_struct_0(k2_yellow_1(B_711)) | v1_xboole_0(B_711) | ~m1_subset_1(k3_tarski(B_711), B_711))), inference(resolution, [status(thm)], [c_4407, c_661])).
% 8.18/2.92  tff(c_4486, plain, (![A_710]: (r1_tarski(A_710, k3_tarski('#skF_5')) | ~m1_subset_1(A_710, '#skF_5') | v2_struct_0(k2_yellow_1('#skF_5')) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_131, c_4484])).
% 8.18/2.92  tff(c_4523, plain, (![A_717]: (r1_tarski(A_717, k3_tarski('#skF_5')) | ~m1_subset_1(A_717, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_1769, c_4486])).
% 8.18/2.92  tff(c_139, plain, (![A_106]: (k2_yellow_0(A_106, k1_xboole_0)=k4_yellow_0(A_106) | ~l1_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.18/2.92  tff(c_143, plain, (![A_80]: (k2_yellow_0(k2_yellow_1(A_80), k1_xboole_0)=k4_yellow_0(k2_yellow_1(A_80)))), inference(resolution, [status(thm)], [c_66, c_139])).
% 8.18/2.92  tff(c_1408, plain, (![A_390, D_391, B_392]: (r1_orders_2(A_390, D_391, k2_yellow_0(A_390, B_392)) | ~r1_lattice3(A_390, B_392, D_391) | ~m1_subset_1(D_391, u1_struct_0(A_390)) | ~r2_yellow_0(A_390, B_392) | ~m1_subset_1(k2_yellow_0(A_390, B_392), u1_struct_0(A_390)) | ~l1_orders_2(A_390))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.18/2.92  tff(c_1410, plain, (![A_80, D_391]: (r1_orders_2(k2_yellow_1(A_80), D_391, k2_yellow_0(k2_yellow_1(A_80), k1_xboole_0)) | ~r1_lattice3(k2_yellow_1(A_80), k1_xboole_0, D_391) | ~m1_subset_1(D_391, u1_struct_0(k2_yellow_1(A_80))) | ~r2_yellow_0(k2_yellow_1(A_80), k1_xboole_0) | ~m1_subset_1(k4_yellow_0(k2_yellow_1(A_80)), u1_struct_0(k2_yellow_1(A_80))) | ~l1_orders_2(k2_yellow_1(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_1408])).
% 8.18/2.92  tff(c_1417, plain, (![A_393, D_394]: (r1_orders_2(k2_yellow_1(A_393), D_394, k4_yellow_0(k2_yellow_1(A_393))) | ~r1_lattice3(k2_yellow_1(A_393), k1_xboole_0, D_394) | ~m1_subset_1(D_394, A_393) | ~r2_yellow_0(k2_yellow_1(A_393), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_137, c_80, c_80, c_143, c_1410])).
% 8.18/2.92  tff(c_562, plain, (![C_90, B_88, A_84]: (C_90=B_88 | ~r1_orders_2(k2_yellow_1(A_84), C_90, B_88) | v2_struct_0(k2_yellow_1(A_84)) | ~r1_tarski(B_88, C_90) | ~m1_subset_1(C_90, A_84) | ~m1_subset_1(B_88, A_84) | v1_xboole_0(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_80, c_80, c_555])).
% 8.18/2.92  tff(c_1438, plain, (![A_393, D_394]: (k4_yellow_0(k2_yellow_1(A_393))=D_394 | v2_struct_0(k2_yellow_1(A_393)) | ~r1_tarski(k4_yellow_0(k2_yellow_1(A_393)), D_394) | ~m1_subset_1(k4_yellow_0(k2_yellow_1(A_393)), A_393) | v1_xboole_0(A_393) | ~r1_lattice3(k2_yellow_1(A_393), k1_xboole_0, D_394) | ~m1_subset_1(D_394, A_393) | ~r2_yellow_0(k2_yellow_1(A_393), k1_xboole_0))), inference(resolution, [status(thm)], [c_1417, c_562])).
% 8.18/2.92  tff(c_1464, plain, (![A_393, D_394]: (k4_yellow_0(k2_yellow_1(A_393))=D_394 | v2_struct_0(k2_yellow_1(A_393)) | ~r1_tarski(k4_yellow_0(k2_yellow_1(A_393)), D_394) | v1_xboole_0(A_393) | ~r1_lattice3(k2_yellow_1(A_393), k1_xboole_0, D_394) | ~m1_subset_1(D_394, A_393) | ~r2_yellow_0(k2_yellow_1(A_393), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_1438])).
% 8.18/2.92  tff(c_5042, plain, (![A_757]: (k4_yellow_0(k2_yellow_1(A_757))=k3_tarski('#skF_5') | v2_struct_0(k2_yellow_1(A_757)) | v1_xboole_0(A_757) | ~r1_lattice3(k2_yellow_1(A_757), k1_xboole_0, k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), A_757) | ~r2_yellow_0(k2_yellow_1(A_757), k1_xboole_0) | ~m1_subset_1(k4_yellow_0(k2_yellow_1(A_757)), '#skF_5'))), inference(resolution, [status(thm)], [c_4523, c_1464])).
% 8.18/2.92  tff(c_5161, plain, (![A_768]: (k4_yellow_0(k2_yellow_1(A_768))=k3_tarski('#skF_5') | v2_struct_0(k2_yellow_1(A_768)) | v1_xboole_0(A_768) | ~r2_yellow_0(k2_yellow_1(A_768), k1_xboole_0) | ~m1_subset_1(k4_yellow_0(k2_yellow_1(A_768)), '#skF_5') | ~m1_subset_1(k3_tarski('#skF_5'), A_768))), inference(resolution, [status(thm)], [c_296, c_5042])).
% 8.18/2.92  tff(c_5165, plain, (k4_yellow_0(k2_yellow_1('#skF_5'))=k3_tarski('#skF_5') | v2_struct_0(k2_yellow_1('#skF_5')) | v1_xboole_0('#skF_5') | ~r2_yellow_0(k2_yellow_1('#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_tarski('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_137, c_5161])).
% 8.18/2.92  tff(c_5168, plain, (k4_yellow_0(k2_yellow_1('#skF_5'))=k3_tarski('#skF_5') | v2_struct_0(k2_yellow_1('#skF_5')) | v1_xboole_0('#skF_5') | ~r2_yellow_0(k2_yellow_1('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_5165])).
% 8.18/2.92  tff(c_5169, plain, (~r2_yellow_0(k2_yellow_1('#skF_5'), k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_92, c_1769, c_88, c_5168])).
% 8.18/2.92  tff(c_518, plain, (![A_263, B_264, C_265]: (m1_subset_1('#skF_4'(A_263, B_264, C_265), u1_struct_0(A_263)) | r2_yellow_0(A_263, C_265) | ~r1_lattice3(A_263, C_265, B_264) | ~m1_subset_1(B_264, u1_struct_0(A_263)) | ~l1_orders_2(A_263) | ~v5_orders_2(A_263))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.18/2.92  tff(c_527, plain, (![A_83, B_264, C_265]: (m1_subset_1('#skF_4'(k2_yellow_1(A_83), B_264, C_265), A_83) | r2_yellow_0(k2_yellow_1(A_83), C_265) | ~r1_lattice3(k2_yellow_1(A_83), C_265, B_264) | ~m1_subset_1(B_264, u1_struct_0(k2_yellow_1(A_83))) | ~l1_orders_2(k2_yellow_1(A_83)) | ~v5_orders_2(k2_yellow_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_518])).
% 8.18/2.92  tff(c_531, plain, (![A_83, B_264, C_265]: (m1_subset_1('#skF_4'(k2_yellow_1(A_83), B_264, C_265), A_83) | r2_yellow_0(k2_yellow_1(A_83), C_265) | ~r1_lattice3(k2_yellow_1(A_83), C_265, B_264) | ~m1_subset_1(B_264, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_80, c_527])).
% 8.18/2.92  tff(c_445, plain, (![A_208, B_39, C_210]: (r2_lattice3(k2_yellow_1(A_208), B_39, C_210) | v2_struct_0(k2_yellow_1(A_208)) | ~r1_tarski('#skF_2'(k2_yellow_1(A_208), B_39, C_210), C_210) | ~m1_subset_1(C_210, A_208) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_208), B_39, C_210), A_208) | v1_xboole_0(A_208))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80, c_439])).
% 8.18/2.92  tff(c_5495, plain, (![A_792, B_793]: (r2_lattice3(k2_yellow_1(A_792), B_793, k3_tarski('#skF_5')) | v2_struct_0(k2_yellow_1(A_792)) | ~m1_subset_1(k3_tarski('#skF_5'), A_792) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_792), B_793, k3_tarski('#skF_5')), A_792) | v1_xboole_0(A_792) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_792), B_793, k3_tarski('#skF_5')), '#skF_5'))), inference(resolution, [status(thm)], [c_4523, c_445])).
% 8.18/2.92  tff(c_5498, plain, (![B_124]: (v2_struct_0(k2_yellow_1(B_124)) | ~m1_subset_1(k3_tarski('#skF_5'), B_124) | v1_xboole_0(B_124) | ~m1_subset_1('#skF_2'(k2_yellow_1(B_124), B_124, k3_tarski('#skF_5')), '#skF_5') | r2_lattice3(k2_yellow_1(B_124), B_124, k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), u1_struct_0(k2_yellow_1(B_124))) | ~l1_orders_2(k2_yellow_1(B_124)))), inference(resolution, [status(thm)], [c_213, c_5495])).
% 8.18/2.92  tff(c_5506, plain, (![B_794]: (v2_struct_0(k2_yellow_1(B_794)) | v1_xboole_0(B_794) | ~m1_subset_1('#skF_2'(k2_yellow_1(B_794), B_794, k3_tarski('#skF_5')), '#skF_5') | r2_lattice3(k2_yellow_1(B_794), B_794, k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), B_794))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_80, c_5498])).
% 8.18/2.92  tff(c_5510, plain, (v2_struct_0(k2_yellow_1('#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(k3_tarski('#skF_5'), '#skF_5') | r2_lattice3(k2_yellow_1('#skF_5'), '#skF_5', k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), u1_struct_0(k2_yellow_1('#skF_5'))) | ~l1_orders_2(k2_yellow_1('#skF_5'))), inference(resolution, [status(thm)], [c_213, c_5506])).
% 8.18/2.92  tff(c_5517, plain, (v2_struct_0(k2_yellow_1('#skF_5')) | v1_xboole_0('#skF_5') | r2_lattice3(k2_yellow_1('#skF_5'), '#skF_5', k3_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_131, c_80, c_131, c_5510])).
% 8.18/2.92  tff(c_5518, plain, (r2_lattice3(k2_yellow_1('#skF_5'), '#skF_5', k3_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_1769, c_5517])).
% 8.18/2.92  tff(c_5534, plain, (![A_341]: (r1_orders_2(k2_yellow_1('#skF_5'), A_341, k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5') | ~m1_subset_1(A_341, '#skF_5'))), inference(resolution, [status(thm)], [c_5518, c_877])).
% 8.18/2.92  tff(c_5565, plain, (![A_341]: (r1_orders_2(k2_yellow_1('#skF_5'), A_341, k3_tarski('#skF_5')) | v1_xboole_0('#skF_5') | ~m1_subset_1(A_341, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_5534])).
% 8.18/2.92  tff(c_5772, plain, (![A_800]: (r1_orders_2(k2_yellow_1('#skF_5'), A_800, k3_tarski('#skF_5')) | ~m1_subset_1(A_800, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_92, c_5565])).
% 8.18/2.92  tff(c_52, plain, (![A_58, B_70, C_76]: (~r1_orders_2(A_58, '#skF_4'(A_58, B_70, C_76), B_70) | r2_yellow_0(A_58, C_76) | ~r1_lattice3(A_58, C_76, B_70) | ~m1_subset_1(B_70, u1_struct_0(A_58)) | ~l1_orders_2(A_58) | ~v5_orders_2(A_58))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.18/2.92  tff(c_5815, plain, (![C_76]: (r2_yellow_0(k2_yellow_1('#skF_5'), C_76) | ~r1_lattice3(k2_yellow_1('#skF_5'), C_76, k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), u1_struct_0(k2_yellow_1('#skF_5'))) | ~l1_orders_2(k2_yellow_1('#skF_5')) | ~v5_orders_2(k2_yellow_1('#skF_5')) | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5'), k3_tarski('#skF_5'), C_76), '#skF_5'))), inference(resolution, [status(thm)], [c_5772, c_52])).
% 8.18/2.92  tff(c_6243, plain, (![C_810]: (r2_yellow_0(k2_yellow_1('#skF_5'), C_810) | ~r1_lattice3(k2_yellow_1('#skF_5'), C_810, k3_tarski('#skF_5')) | ~m1_subset_1('#skF_4'(k2_yellow_1('#skF_5'), k3_tarski('#skF_5'), C_810), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_66, c_131, c_80, c_5815])).
% 8.18/2.92  tff(c_6251, plain, (![C_265]: (r2_yellow_0(k2_yellow_1('#skF_5'), C_265) | ~r1_lattice3(k2_yellow_1('#skF_5'), C_265, k3_tarski('#skF_5')) | ~m1_subset_1(k3_tarski('#skF_5'), '#skF_5'))), inference(resolution, [status(thm)], [c_531, c_6243])).
% 8.18/2.92  tff(c_6258, plain, (![C_811]: (r2_yellow_0(k2_yellow_1('#skF_5'), C_811) | ~r1_lattice3(k2_yellow_1('#skF_5'), C_811, k3_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_6251])).
% 8.18/2.92  tff(c_6262, plain, (r2_yellow_0(k2_yellow_1('#skF_5'), k1_xboole_0) | ~m1_subset_1(k3_tarski('#skF_5'), '#skF_5')), inference(resolution, [status(thm)], [c_296, c_6258])).
% 8.18/2.92  tff(c_6265, plain, (r2_yellow_0(k2_yellow_1('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_131, c_6262])).
% 8.18/2.92  tff(c_6267, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5169, c_6265])).
% 8.18/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.18/2.92  
% 8.18/2.92  Inference rules
% 8.18/2.92  ----------------------
% 8.18/2.92  #Ref     : 0
% 8.18/2.92  #Sup     : 1142
% 8.18/2.92  #Fact    : 0
% 8.18/2.92  #Define  : 0
% 8.18/2.92  #Split   : 7
% 8.18/2.92  #Chain   : 0
% 8.18/2.92  #Close   : 0
% 8.18/2.92  
% 8.18/2.92  Ordering : KBO
% 8.18/2.92  
% 8.18/2.92  Simplification rules
% 8.18/2.92  ----------------------
% 8.18/2.92  #Subsume      : 143
% 8.18/2.92  #Demod        : 1979
% 8.18/2.92  #Tautology    : 322
% 8.18/2.92  #SimpNegUnit  : 74
% 8.18/2.92  #BackRed      : 27
% 8.18/2.92  
% 8.18/2.92  #Partial instantiations: 0
% 8.18/2.92  #Strategies tried      : 1
% 8.18/2.92  
% 8.18/2.92  Timing (in seconds)
% 8.18/2.92  ----------------------
% 8.18/2.93  Preprocessing        : 0.38
% 8.18/2.93  Parsing              : 0.19
% 8.18/2.93  CNF conversion       : 0.03
% 8.18/2.93  Main loop            : 1.77
% 8.18/2.93  Inferencing          : 0.67
% 8.18/2.93  Reduction            : 0.56
% 8.18/2.93  Demodulation         : 0.39
% 8.18/2.93  BG Simplification    : 0.07
% 8.18/2.93  Subsumption          : 0.37
% 8.18/2.93  Abstraction          : 0.08
% 8.18/2.93  MUC search           : 0.00
% 8.18/2.93  Cooper               : 0.00
% 8.18/2.93  Total                : 2.20
% 8.18/2.93  Index Insertion      : 0.00
% 8.18/2.93  Index Deletion       : 0.00
% 8.18/2.93  Index Matching       : 0.00
% 8.18/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
