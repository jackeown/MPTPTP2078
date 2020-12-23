%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:28 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   41 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  200 ( 316 expanded)
%              Number of equality atoms :   23 (  61 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

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

tff(f_155,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k3_tarski(A),A)
         => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k4_yellow_0(A) = k2_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).

tff(f_134,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_101,axiom,(
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

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_147,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_130,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_64,plain,(
    k4_yellow_0(k2_yellow_1('#skF_2')) != k3_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_66,plain,(
    r2_hidden(k3_tarski('#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_109,plain,(
    ! [B_62,A_63] :
      ( m1_subset_1(B_62,A_63)
      | ~ r2_hidden(B_62,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_112,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_109])).

tff(c_115,plain,(
    m1_subset_1(k3_tarski('#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_112])).

tff(c_42,plain,(
    ! [A_36] : l1_orders_2(k2_yellow_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_99,plain,(
    ! [A_59] :
      ( k2_yellow_0(A_59,k1_xboole_0) = k4_yellow_0(A_59)
      | ~ l1_orders_2(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_103,plain,(
    ! [A_36] : k2_yellow_0(k2_yellow_1(A_36),k1_xboole_0) = k4_yellow_0(k2_yellow_1(A_36)) ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_56,plain,(
    ! [A_39] : u1_struct_0(k2_yellow_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_146,plain,(
    ! [A_71,B_72] :
      ( r1_lattice3(A_71,k1_xboole_0,B_72)
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_orders_2(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_153,plain,(
    ! [A_39,B_72] :
      ( r1_lattice3(k2_yellow_1(A_39),k1_xboole_0,B_72)
      | ~ m1_subset_1(B_72,A_39)
      | ~ l1_orders_2(k2_yellow_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_146])).

tff(c_156,plain,(
    ! [A_39,B_72] :
      ( r1_lattice3(k2_yellow_1(A_39),k1_xboole_0,B_72)
      | ~ m1_subset_1(B_72,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_153])).

tff(c_50,plain,(
    ! [A_37] : v5_orders_2(k2_yellow_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_292,plain,(
    ! [A_137,B_138,C_139] :
      ( m1_subset_1('#skF_1'(A_137,B_138,C_139),u1_struct_0(A_137))
      | k2_yellow_0(A_137,C_139) = B_138
      | ~ r1_lattice3(A_137,C_139,B_138)
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_306,plain,(
    ! [A_39,B_138,C_139] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_39),B_138,C_139),A_39)
      | k2_yellow_0(k2_yellow_1(A_39),C_139) = B_138
      | ~ r1_lattice3(k2_yellow_1(A_39),C_139,B_138)
      | ~ m1_subset_1(B_138,u1_struct_0(k2_yellow_1(A_39)))
      | ~ l1_orders_2(k2_yellow_1(A_39))
      | ~ v5_orders_2(k2_yellow_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_292])).

tff(c_312,plain,(
    ! [A_39,B_138,C_139] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_39),B_138,C_139),A_39)
      | k2_yellow_0(k2_yellow_1(A_39),C_139) = B_138
      | ~ r1_lattice3(k2_yellow_1(A_39),C_139,B_138)
      | ~ m1_subset_1(B_138,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_56,c_306])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,k3_tarski(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_46,plain,(
    ! [A_37] : v3_orders_2(k2_yellow_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    ! [A_40,B_44,C_46] :
      ( r3_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(k2_yellow_1(A_40)))
      | ~ m1_subset_1(B_44,u1_struct_0(k2_yellow_1(A_40)))
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_70,plain,(
    ! [A_40,B_44,C_46] :
      ( r3_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1(B_44,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_60])).

tff(c_220,plain,(
    ! [A_104,B_105,C_106] :
      ( r1_orders_2(A_104,B_105,C_106)
      | ~ r3_orders_2(A_104,B_105,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_104))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_222,plain,(
    ! [A_40,B_44,C_46] :
      ( r1_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(k2_yellow_1(A_40)))
      | ~ m1_subset_1(B_44,u1_struct_0(k2_yellow_1(A_40)))
      | ~ l1_orders_2(k2_yellow_1(A_40))
      | ~ v3_orders_2(k2_yellow_1(A_40))
      | v2_struct_0(k2_yellow_1(A_40))
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1(B_44,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_70,c_220])).

tff(c_225,plain,(
    ! [A_40,B_44,C_46] :
      ( r1_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | v2_struct_0(k2_yellow_1(A_40))
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1(B_44,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_56,c_56,c_222])).

tff(c_284,plain,(
    ! [A_134,B_135,C_136] :
      ( ~ r1_orders_2(A_134,'#skF_1'(A_134,B_135,C_136),B_135)
      | k2_yellow_0(A_134,C_136) = B_135
      | ~ r1_lattice3(A_134,C_136,B_135)
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v5_orders_2(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_288,plain,(
    ! [A_40,C_136,C_46] :
      ( k2_yellow_0(k2_yellow_1(A_40),C_136) = C_46
      | ~ r1_lattice3(k2_yellow_1(A_40),C_136,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(k2_yellow_1(A_40)))
      | ~ l1_orders_2(k2_yellow_1(A_40))
      | ~ v5_orders_2(k2_yellow_1(A_40))
      | v2_struct_0(k2_yellow_1(A_40))
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_40),C_46,C_136),C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_40),C_46,C_136),A_40)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_225,c_284])).

tff(c_595,plain,(
    ! [A_231,C_232,C_233] :
      ( k2_yellow_0(k2_yellow_1(A_231),C_232) = C_233
      | ~ r1_lattice3(k2_yellow_1(A_231),C_232,C_233)
      | v2_struct_0(k2_yellow_1(A_231))
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_231),C_233,C_232),C_233)
      | ~ m1_subset_1(C_233,A_231)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_231),C_233,C_232),A_231)
      | v1_xboole_0(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_56,c_288])).

tff(c_684,plain,(
    ! [B_258,A_259,C_260] :
      ( k3_tarski(B_258) = k2_yellow_0(k2_yellow_1(A_259),C_260)
      | ~ r1_lattice3(k2_yellow_1(A_259),C_260,k3_tarski(B_258))
      | v2_struct_0(k2_yellow_1(A_259))
      | ~ m1_subset_1(k3_tarski(B_258),A_259)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_259),k3_tarski(B_258),C_260),A_259)
      | v1_xboole_0(A_259)
      | ~ r2_hidden('#skF_1'(k2_yellow_1(A_259),k3_tarski(B_258),C_260),B_258) ) ),
    inference(resolution,[status(thm)],[c_2,c_595])).

tff(c_697,plain,(
    ! [A_261,B_262,C_263] :
      ( v2_struct_0(k2_yellow_1(A_261))
      | v1_xboole_0(A_261)
      | ~ r2_hidden('#skF_1'(k2_yellow_1(A_261),k3_tarski(B_262),C_263),B_262)
      | k3_tarski(B_262) = k2_yellow_0(k2_yellow_1(A_261),C_263)
      | ~ r1_lattice3(k2_yellow_1(A_261),C_263,k3_tarski(B_262))
      | ~ m1_subset_1(k3_tarski(B_262),A_261) ) ),
    inference(resolution,[status(thm)],[c_312,c_684])).

tff(c_714,plain,(
    ! [A_268,B_269,C_270] :
      ( v2_struct_0(k2_yellow_1(A_268))
      | v1_xboole_0(A_268)
      | k3_tarski(B_269) = k2_yellow_0(k2_yellow_1(A_268),C_270)
      | ~ r1_lattice3(k2_yellow_1(A_268),C_270,k3_tarski(B_269))
      | ~ m1_subset_1(k3_tarski(B_269),A_268)
      | v1_xboole_0(B_269)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_268),k3_tarski(B_269),C_270),B_269) ) ),
    inference(resolution,[status(thm)],[c_12,c_697])).

tff(c_744,plain,(
    ! [A_271,C_272] :
      ( v2_struct_0(k2_yellow_1(A_271))
      | v1_xboole_0(A_271)
      | k2_yellow_0(k2_yellow_1(A_271),C_272) = k3_tarski(A_271)
      | ~ r1_lattice3(k2_yellow_1(A_271),C_272,k3_tarski(A_271))
      | ~ m1_subset_1(k3_tarski(A_271),A_271) ) ),
    inference(resolution,[status(thm)],[c_312,c_714])).

tff(c_752,plain,(
    ! [A_39] :
      ( v2_struct_0(k2_yellow_1(A_39))
      | v1_xboole_0(A_39)
      | k2_yellow_0(k2_yellow_1(A_39),k1_xboole_0) = k3_tarski(A_39)
      | ~ m1_subset_1(k3_tarski(A_39),A_39) ) ),
    inference(resolution,[status(thm)],[c_156,c_744])).

tff(c_757,plain,(
    ! [A_273] :
      ( v2_struct_0(k2_yellow_1(A_273))
      | v1_xboole_0(A_273)
      | k4_yellow_0(k2_yellow_1(A_273)) = k3_tarski(A_273)
      | ~ m1_subset_1(k3_tarski(A_273),A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_752])).

tff(c_760,plain,
    ( v2_struct_0(k2_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_2')
    | k4_yellow_0(k2_yellow_1('#skF_2')) = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_115,c_757])).

tff(c_767,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_68,c_760])).

tff(c_54,plain,(
    ! [A_38] :
      ( ~ v2_struct_0(k2_yellow_1(A_38))
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_771,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_767,c_54])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.84/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.64  
% 3.84/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.64  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.84/1.64  
% 3.84/1.64  %Foreground sorts:
% 3.84/1.64  
% 3.84/1.64  
% 3.84/1.64  %Background operators:
% 3.84/1.64  
% 3.84/1.64  
% 3.84/1.64  %Foreground operators:
% 3.84/1.64  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.84/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.84/1.64  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.84/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.84/1.64  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.84/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.84/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.84/1.64  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.84/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.84/1.64  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.84/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.84/1.64  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.84/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.84/1.64  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 3.84/1.64  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 3.84/1.64  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.84/1.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.84/1.64  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.84/1.64  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.84/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.84/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.84/1.64  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 3.84/1.64  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.84/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.84/1.64  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.84/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.84/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.84/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.84/1.64  
% 3.84/1.66  tff(f_155, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 3.84/1.66  tff(f_42, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.84/1.66  tff(f_114, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.84/1.66  tff(f_67, axiom, (![A]: (l1_orders_2(A) => (k4_yellow_0(A) = k2_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_yellow_0)).
% 3.84/1.66  tff(f_134, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.84/1.66  tff(f_110, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.84/1.66  tff(f_122, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.84/1.66  tff(f_101, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C)) => (r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B)))))) & ((r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B))))) => ((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 3.84/1.66  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.84/1.66  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.84/1.66  tff(f_147, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.84/1.66  tff(f_63, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.84/1.66  tff(f_130, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.84/1.66  tff(c_68, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.84/1.66  tff(c_64, plain, (k4_yellow_0(k2_yellow_1('#skF_2'))!=k3_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.84/1.66  tff(c_66, plain, (r2_hidden(k3_tarski('#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.84/1.66  tff(c_109, plain, (![B_62, A_63]: (m1_subset_1(B_62, A_63) | ~r2_hidden(B_62, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.84/1.66  tff(c_112, plain, (m1_subset_1(k3_tarski('#skF_2'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_109])).
% 3.84/1.66  tff(c_115, plain, (m1_subset_1(k3_tarski('#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_112])).
% 3.84/1.66  tff(c_42, plain, (![A_36]: (l1_orders_2(k2_yellow_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.84/1.66  tff(c_99, plain, (![A_59]: (k2_yellow_0(A_59, k1_xboole_0)=k4_yellow_0(A_59) | ~l1_orders_2(A_59))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.84/1.66  tff(c_103, plain, (![A_36]: (k2_yellow_0(k2_yellow_1(A_36), k1_xboole_0)=k4_yellow_0(k2_yellow_1(A_36)))), inference(resolution, [status(thm)], [c_42, c_99])).
% 3.84/1.66  tff(c_56, plain, (![A_39]: (u1_struct_0(k2_yellow_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.84/1.66  tff(c_146, plain, (![A_71, B_72]: (r1_lattice3(A_71, k1_xboole_0, B_72) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_orders_2(A_71))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.84/1.66  tff(c_153, plain, (![A_39, B_72]: (r1_lattice3(k2_yellow_1(A_39), k1_xboole_0, B_72) | ~m1_subset_1(B_72, A_39) | ~l1_orders_2(k2_yellow_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_146])).
% 3.84/1.66  tff(c_156, plain, (![A_39, B_72]: (r1_lattice3(k2_yellow_1(A_39), k1_xboole_0, B_72) | ~m1_subset_1(B_72, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_153])).
% 3.84/1.66  tff(c_50, plain, (![A_37]: (v5_orders_2(k2_yellow_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.84/1.66  tff(c_292, plain, (![A_137, B_138, C_139]: (m1_subset_1('#skF_1'(A_137, B_138, C_139), u1_struct_0(A_137)) | k2_yellow_0(A_137, C_139)=B_138 | ~r1_lattice3(A_137, C_139, B_138) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v5_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.84/1.66  tff(c_306, plain, (![A_39, B_138, C_139]: (m1_subset_1('#skF_1'(k2_yellow_1(A_39), B_138, C_139), A_39) | k2_yellow_0(k2_yellow_1(A_39), C_139)=B_138 | ~r1_lattice3(k2_yellow_1(A_39), C_139, B_138) | ~m1_subset_1(B_138, u1_struct_0(k2_yellow_1(A_39))) | ~l1_orders_2(k2_yellow_1(A_39)) | ~v5_orders_2(k2_yellow_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_292])).
% 3.84/1.66  tff(c_312, plain, (![A_39, B_138, C_139]: (m1_subset_1('#skF_1'(k2_yellow_1(A_39), B_138, C_139), A_39) | k2_yellow_0(k2_yellow_1(A_39), C_139)=B_138 | ~r1_lattice3(k2_yellow_1(A_39), C_139, B_138) | ~m1_subset_1(B_138, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_56, c_306])).
% 3.84/1.66  tff(c_12, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.84/1.66  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k3_tarski(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.84/1.66  tff(c_46, plain, (![A_37]: (v3_orders_2(k2_yellow_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.84/1.66  tff(c_60, plain, (![A_40, B_44, C_46]: (r3_orders_2(k2_yellow_1(A_40), B_44, C_46) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, u1_struct_0(k2_yellow_1(A_40))) | ~m1_subset_1(B_44, u1_struct_0(k2_yellow_1(A_40))) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.84/1.66  tff(c_70, plain, (![A_40, B_44, C_46]: (r3_orders_2(k2_yellow_1(A_40), B_44, C_46) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1(B_44, A_40) | v1_xboole_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_60])).
% 3.84/1.66  tff(c_220, plain, (![A_104, B_105, C_106]: (r1_orders_2(A_104, B_105, C_106) | ~r3_orders_2(A_104, B_105, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_104)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.84/1.66  tff(c_222, plain, (![A_40, B_44, C_46]: (r1_orders_2(k2_yellow_1(A_40), B_44, C_46) | ~m1_subset_1(C_46, u1_struct_0(k2_yellow_1(A_40))) | ~m1_subset_1(B_44, u1_struct_0(k2_yellow_1(A_40))) | ~l1_orders_2(k2_yellow_1(A_40)) | ~v3_orders_2(k2_yellow_1(A_40)) | v2_struct_0(k2_yellow_1(A_40)) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1(B_44, A_40) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_70, c_220])).
% 3.84/1.66  tff(c_225, plain, (![A_40, B_44, C_46]: (r1_orders_2(k2_yellow_1(A_40), B_44, C_46) | v2_struct_0(k2_yellow_1(A_40)) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1(B_44, A_40) | v1_xboole_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42, c_56, c_56, c_222])).
% 3.84/1.66  tff(c_284, plain, (![A_134, B_135, C_136]: (~r1_orders_2(A_134, '#skF_1'(A_134, B_135, C_136), B_135) | k2_yellow_0(A_134, C_136)=B_135 | ~r1_lattice3(A_134, C_136, B_135) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v5_orders_2(A_134))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.84/1.66  tff(c_288, plain, (![A_40, C_136, C_46]: (k2_yellow_0(k2_yellow_1(A_40), C_136)=C_46 | ~r1_lattice3(k2_yellow_1(A_40), C_136, C_46) | ~m1_subset_1(C_46, u1_struct_0(k2_yellow_1(A_40))) | ~l1_orders_2(k2_yellow_1(A_40)) | ~v5_orders_2(k2_yellow_1(A_40)) | v2_struct_0(k2_yellow_1(A_40)) | ~r1_tarski('#skF_1'(k2_yellow_1(A_40), C_46, C_136), C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_40), C_46, C_136), A_40) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_225, c_284])).
% 3.84/1.66  tff(c_595, plain, (![A_231, C_232, C_233]: (k2_yellow_0(k2_yellow_1(A_231), C_232)=C_233 | ~r1_lattice3(k2_yellow_1(A_231), C_232, C_233) | v2_struct_0(k2_yellow_1(A_231)) | ~r1_tarski('#skF_1'(k2_yellow_1(A_231), C_233, C_232), C_233) | ~m1_subset_1(C_233, A_231) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_231), C_233, C_232), A_231) | v1_xboole_0(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_56, c_288])).
% 3.84/1.66  tff(c_684, plain, (![B_258, A_259, C_260]: (k3_tarski(B_258)=k2_yellow_0(k2_yellow_1(A_259), C_260) | ~r1_lattice3(k2_yellow_1(A_259), C_260, k3_tarski(B_258)) | v2_struct_0(k2_yellow_1(A_259)) | ~m1_subset_1(k3_tarski(B_258), A_259) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_259), k3_tarski(B_258), C_260), A_259) | v1_xboole_0(A_259) | ~r2_hidden('#skF_1'(k2_yellow_1(A_259), k3_tarski(B_258), C_260), B_258))), inference(resolution, [status(thm)], [c_2, c_595])).
% 3.84/1.66  tff(c_697, plain, (![A_261, B_262, C_263]: (v2_struct_0(k2_yellow_1(A_261)) | v1_xboole_0(A_261) | ~r2_hidden('#skF_1'(k2_yellow_1(A_261), k3_tarski(B_262), C_263), B_262) | k3_tarski(B_262)=k2_yellow_0(k2_yellow_1(A_261), C_263) | ~r1_lattice3(k2_yellow_1(A_261), C_263, k3_tarski(B_262)) | ~m1_subset_1(k3_tarski(B_262), A_261))), inference(resolution, [status(thm)], [c_312, c_684])).
% 3.84/1.66  tff(c_714, plain, (![A_268, B_269, C_270]: (v2_struct_0(k2_yellow_1(A_268)) | v1_xboole_0(A_268) | k3_tarski(B_269)=k2_yellow_0(k2_yellow_1(A_268), C_270) | ~r1_lattice3(k2_yellow_1(A_268), C_270, k3_tarski(B_269)) | ~m1_subset_1(k3_tarski(B_269), A_268) | v1_xboole_0(B_269) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_268), k3_tarski(B_269), C_270), B_269))), inference(resolution, [status(thm)], [c_12, c_697])).
% 3.84/1.66  tff(c_744, plain, (![A_271, C_272]: (v2_struct_0(k2_yellow_1(A_271)) | v1_xboole_0(A_271) | k2_yellow_0(k2_yellow_1(A_271), C_272)=k3_tarski(A_271) | ~r1_lattice3(k2_yellow_1(A_271), C_272, k3_tarski(A_271)) | ~m1_subset_1(k3_tarski(A_271), A_271))), inference(resolution, [status(thm)], [c_312, c_714])).
% 3.84/1.66  tff(c_752, plain, (![A_39]: (v2_struct_0(k2_yellow_1(A_39)) | v1_xboole_0(A_39) | k2_yellow_0(k2_yellow_1(A_39), k1_xboole_0)=k3_tarski(A_39) | ~m1_subset_1(k3_tarski(A_39), A_39))), inference(resolution, [status(thm)], [c_156, c_744])).
% 3.84/1.66  tff(c_757, plain, (![A_273]: (v2_struct_0(k2_yellow_1(A_273)) | v1_xboole_0(A_273) | k4_yellow_0(k2_yellow_1(A_273))=k3_tarski(A_273) | ~m1_subset_1(k3_tarski(A_273), A_273))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_752])).
% 3.84/1.66  tff(c_760, plain, (v2_struct_0(k2_yellow_1('#skF_2')) | v1_xboole_0('#skF_2') | k4_yellow_0(k2_yellow_1('#skF_2'))=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_115, c_757])).
% 3.84/1.66  tff(c_767, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_64, c_68, c_760])).
% 3.84/1.66  tff(c_54, plain, (![A_38]: (~v2_struct_0(k2_yellow_1(A_38)) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.84/1.66  tff(c_771, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_767, c_54])).
% 3.84/1.66  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_771])).
% 3.84/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/1.66  
% 3.84/1.66  Inference rules
% 3.84/1.66  ----------------------
% 3.84/1.66  #Ref     : 0
% 3.84/1.66  #Sup     : 133
% 3.84/1.66  #Fact    : 0
% 3.84/1.66  #Define  : 0
% 3.84/1.66  #Split   : 1
% 3.84/1.66  #Chain   : 0
% 3.84/1.66  #Close   : 0
% 3.84/1.66  
% 3.84/1.66  Ordering : KBO
% 3.84/1.66  
% 3.84/1.66  Simplification rules
% 3.84/1.66  ----------------------
% 3.84/1.66  #Subsume      : 23
% 3.84/1.66  #Demod        : 168
% 3.84/1.66  #Tautology    : 30
% 3.84/1.66  #SimpNegUnit  : 4
% 3.84/1.66  #BackRed      : 0
% 3.84/1.66  
% 3.84/1.66  #Partial instantiations: 0
% 3.84/1.66  #Strategies tried      : 1
% 3.84/1.66  
% 3.84/1.66  Timing (in seconds)
% 3.84/1.66  ----------------------
% 3.84/1.67  Preprocessing        : 0.37
% 3.84/1.67  Parsing              : 0.19
% 3.84/1.67  CNF conversion       : 0.03
% 3.84/1.67  Main loop            : 0.52
% 3.84/1.67  Inferencing          : 0.21
% 3.84/1.67  Reduction            : 0.14
% 3.84/1.67  Demodulation         : 0.10
% 3.84/1.67  BG Simplification    : 0.03
% 3.84/1.67  Subsumption          : 0.10
% 3.84/1.67  Abstraction          : 0.03
% 3.84/1.67  MUC search           : 0.00
% 3.84/1.67  Cooper               : 0.00
% 3.84/1.67  Total                : 0.93
% 3.84/1.67  Index Insertion      : 0.00
% 3.84/1.67  Index Deletion       : 0.00
% 3.84/1.67  Index Matching       : 0.00
% 3.84/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
