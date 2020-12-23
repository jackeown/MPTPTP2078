%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:48 EST 2020

% Result     : Theorem 15.37s
% Output     : CNFRefutation 15.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 184 expanded)
%              Number of leaves         :   26 (  83 expanded)
%              Depth                    :   26
%              Number of atoms          :  340 ( 907 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                   => ( r1_tarski(C,D)
                     => r1_tarski(k3_orders_2(A,C,B),k3_orders_2(A,D,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_orders_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k3_orders_2(A,B,C),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_orders_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    v3_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_36,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    v5_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    l1_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k3_orders_2(A_13,B_14,C_15),k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ m1_subset_1(C_15,u1_struct_0(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_orders_2(A_13)
      | ~ v5_orders_2(A_13)
      | ~ v4_orders_2(A_13)
      | ~ v3_orders_2(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [A_44,B_45] :
      ( ~ r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_47,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_12,plain,(
    ! [A_6,B_7,C_11] :
      ( m1_subset_1('#skF_2'(A_6,B_7,C_11),A_6)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_100,plain,(
    ! [A_68,B_69,C_70] :
      ( r2_hidden('#skF_2'(A_68,B_69,C_70),B_69)
      | r1_tarski(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_68,B_69,C_70,B_2] :
      ( r2_hidden('#skF_2'(A_68,B_69,C_70),B_2)
      | ~ r1_tarski(B_69,B_2)
      | r1_tarski(B_69,C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_160,plain,(
    ! [B_102,D_103,A_104,C_105] :
      ( r2_hidden(B_102,D_103)
      | ~ r2_hidden(B_102,k3_orders_2(A_104,D_103,C_105))
      | ~ m1_subset_1(D_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | ~ m1_subset_1(B_102,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v5_orders_2(A_104)
      | ~ v4_orders_2(A_104)
      | ~ v3_orders_2(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_403,plain,(
    ! [A_190,C_185,B_189,A_187,C_188,D_186] :
      ( r2_hidden('#skF_2'(A_190,B_189,C_188),D_186)
      | ~ m1_subset_1(D_186,k1_zfmisc_1(u1_struct_0(A_187)))
      | ~ m1_subset_1(C_185,u1_struct_0(A_187))
      | ~ m1_subset_1('#skF_2'(A_190,B_189,C_188),u1_struct_0(A_187))
      | ~ l1_orders_2(A_187)
      | ~ v5_orders_2(A_187)
      | ~ v4_orders_2(A_187)
      | ~ v3_orders_2(A_187)
      | v2_struct_0(A_187)
      | ~ r1_tarski(B_189,k3_orders_2(A_187,D_186,C_185))
      | r1_tarski(B_189,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_190)) ) ),
    inference(resolution,[status(thm)],[c_103,c_160])).

tff(c_412,plain,(
    ! [A_190,B_189,C_188,C_185] :
      ( r2_hidden('#skF_2'(A_190,B_189,C_188),'#skF_5')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'(A_190,B_189,C_188),u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(B_189,k3_orders_2('#skF_3','#skF_5',C_185))
      | r1_tarski(B_189,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_190)) ) ),
    inference(resolution,[status(thm)],[c_28,c_403])).

tff(c_421,plain,(
    ! [A_190,B_189,C_188,C_185] :
      ( r2_hidden('#skF_2'(A_190,B_189,C_188),'#skF_5')
      | ~ m1_subset_1(C_185,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'(A_190,B_189,C_188),u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r1_tarski(B_189,k3_orders_2('#skF_3','#skF_5',C_185))
      | r1_tarski(B_189,C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(A_190))
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_190)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_412])).

tff(c_594,plain,(
    ! [A_237,B_238,C_239,C_240] :
      ( r2_hidden('#skF_2'(A_237,B_238,C_239),'#skF_5')
      | ~ m1_subset_1(C_240,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'(A_237,B_238,C_239),u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_238,k3_orders_2('#skF_3','#skF_5',C_240))
      | r1_tarski(B_238,C_239)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(A_237))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_237)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_421])).

tff(c_599,plain,(
    ! [B_241,C_242,C_243] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_3'),B_241,C_242),'#skF_5')
      | ~ m1_subset_1(C_243,u1_struct_0('#skF_3'))
      | ~ r1_tarski(B_241,k3_orders_2('#skF_3','#skF_5',C_243))
      | r1_tarski(B_241,C_242)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_594])).

tff(c_617,plain,(
    ! [C_249,C_250] :
      ( r2_hidden('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3','#skF_5',C_249),C_250),'#skF_5')
      | ~ m1_subset_1(C_249,u1_struct_0('#skF_3'))
      | r1_tarski(k3_orders_2('#skF_3','#skF_5',C_249),C_250)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_249),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_47,c_599])).

tff(c_8,plain,(
    ! [A_6,B_7,C_11] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_11),C_11)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_621,plain,(
    ! [C_249] :
      ( ~ m1_subset_1(C_249,u1_struct_0('#skF_3'))
      | r1_tarski(k3_orders_2('#skF_3','#skF_5',C_249),'#skF_5')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_249),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_617,c_8])).

tff(c_628,plain,(
    ! [C_251] :
      ( ~ m1_subset_1(C_251,u1_struct_0('#skF_3'))
      | r1_tarski(k3_orders_2('#skF_3','#skF_5',C_251),'#skF_5')
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_251),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_621])).

tff(c_632,plain,(
    ! [C_15] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_15),'#skF_5')
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_628])).

tff(c_635,plain,(
    ! [C_15] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_15),'#skF_5')
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_632])).

tff(c_637,plain,(
    ! [C_252] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_252),'#skF_5')
      | ~ m1_subset_1(C_252,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_635])).

tff(c_118,plain,(
    ! [A_78,B_79,C_80,B_81] :
      ( r2_hidden('#skF_2'(A_78,B_79,C_80),B_81)
      | ~ r1_tarski(B_79,B_81)
      | r1_tarski(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_126,plain,(
    ! [B_2,C_80,B_81,B_79,A_78] :
      ( r2_hidden('#skF_2'(A_78,B_79,C_80),B_2)
      | ~ r1_tarski(B_81,B_2)
      | ~ r1_tarski(B_79,B_81)
      | r1_tarski(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_694,plain,(
    ! [A_264,B_265,C_266,C_267] :
      ( r2_hidden('#skF_2'(A_264,B_265,C_266),'#skF_5')
      | ~ r1_tarski(B_265,k3_orders_2('#skF_3','#skF_5',C_267))
      | r1_tarski(B_265,C_266)
      | ~ m1_subset_1(C_266,k1_zfmisc_1(A_264))
      | ~ m1_subset_1(B_265,k1_zfmisc_1(A_264))
      | ~ m1_subset_1(C_267,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_637,c_126])).

tff(c_1011,plain,(
    ! [A_322,C_323,C_324] :
      ( r2_hidden('#skF_2'(A_322,k3_orders_2('#skF_3','#skF_5',C_323),C_324),'#skF_5')
      | r1_tarski(k3_orders_2('#skF_3','#skF_5',C_323),C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(A_322))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_323),k1_zfmisc_1(A_322))
      | ~ m1_subset_1(C_323,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_47,c_694])).

tff(c_1019,plain,(
    ! [A_322,C_323,C_324,B_2] :
      ( r2_hidden('#skF_2'(A_322,k3_orders_2('#skF_3','#skF_5',C_323),C_324),B_2)
      | ~ r1_tarski('#skF_5',B_2)
      | r1_tarski(k3_orders_2('#skF_3','#skF_5',C_323),C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(A_322))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_323),k1_zfmisc_1(A_322))
      | ~ m1_subset_1(C_323,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1011,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7,C_11] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_11),B_7)
      | r1_tarski(B_7,C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_185,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( r2_orders_2(A_106,B_107,C_108)
      | ~ r2_hidden(B_107,k3_orders_2(A_106,D_109,C_108))
      | ~ m1_subset_1(D_109,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v4_orders_2(A_106)
      | ~ v3_orders_2(A_106)
      | v2_struct_0(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_660,plain,(
    ! [D_256,A_255,A_257,C_253,C_254] :
      ( r2_orders_2(A_257,'#skF_2'(A_255,k3_orders_2(A_257,D_256,C_253),C_254),C_253)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(u1_struct_0(A_257)))
      | ~ m1_subset_1(C_253,u1_struct_0(A_257))
      | ~ m1_subset_1('#skF_2'(A_255,k3_orders_2(A_257,D_256,C_253),C_254),u1_struct_0(A_257))
      | ~ l1_orders_2(A_257)
      | ~ v5_orders_2(A_257)
      | ~ v4_orders_2(A_257)
      | ~ v3_orders_2(A_257)
      | v2_struct_0(A_257)
      | r1_tarski(k3_orders_2(A_257,D_256,C_253),C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(A_255))
      | ~ m1_subset_1(k3_orders_2(A_257,D_256,C_253),k1_zfmisc_1(A_255)) ) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_1063,plain,(
    ! [A_338,D_339,C_340,C_341] :
      ( r2_orders_2(A_338,'#skF_2'(u1_struct_0(A_338),k3_orders_2(A_338,D_339,C_340),C_341),C_340)
      | ~ m1_subset_1(D_339,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ m1_subset_1(C_340,u1_struct_0(A_338))
      | ~ l1_orders_2(A_338)
      | ~ v5_orders_2(A_338)
      | ~ v4_orders_2(A_338)
      | ~ v3_orders_2(A_338)
      | v2_struct_0(A_338)
      | r1_tarski(k3_orders_2(A_338,D_339,C_340),C_341)
      | ~ m1_subset_1(C_341,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ m1_subset_1(k3_orders_2(A_338,D_339,C_340),k1_zfmisc_1(u1_struct_0(A_338))) ) ),
    inference(resolution,[status(thm)],[c_12,c_660])).

tff(c_210,plain,(
    ! [B_110,A_111,D_112,C_113] :
      ( r2_hidden(B_110,k3_orders_2(A_111,D_112,C_113))
      | ~ r2_hidden(B_110,D_112)
      | ~ r2_orders_2(A_111,B_110,C_113)
      | ~ m1_subset_1(D_112,k1_zfmisc_1(u1_struct_0(A_111)))
      | ~ m1_subset_1(C_113,u1_struct_0(A_111))
      | ~ m1_subset_1(B_110,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_217,plain,(
    ! [B_110,C_113] :
      ( r2_hidden(B_110,k3_orders_2('#skF_3','#skF_6',C_113))
      | ~ r2_hidden(B_110,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_110,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_210])).

tff(c_224,plain,(
    ! [B_110,C_113] :
      ( r2_hidden(B_110,k3_orders_2('#skF_3','#skF_6',C_113))
      | ~ r2_hidden(B_110,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_110,C_113)
      | ~ m1_subset_1(C_113,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_110,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_217])).

tff(c_230,plain,(
    ! [B_114,C_115] :
      ( r2_hidden(B_114,k3_orders_2('#skF_3','#skF_6',C_115))
      | ~ r2_hidden(B_114,'#skF_6')
      | ~ r2_orders_2('#skF_3',B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(B_114,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_224])).

tff(c_253,plain,(
    ! [B_7,C_115,A_6] :
      ( r1_tarski(B_7,k3_orders_2('#skF_3','#skF_6',C_115))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_115),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6))
      | ~ r2_hidden('#skF_2'(A_6,B_7,k3_orders_2('#skF_3','#skF_6',C_115)),'#skF_6')
      | ~ r2_orders_2('#skF_3','#skF_2'(A_6,B_7,k3_orders_2('#skF_3','#skF_6',C_115)),C_115)
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_2'(A_6,B_7,k3_orders_2('#skF_3','#skF_6',C_115)),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_230,c_8])).

tff(c_1066,plain,(
    ! [D_339,C_340] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_339,C_340),k3_orders_2('#skF_3','#skF_6',C_340)),'#skF_6')
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_339,C_340),k3_orders_2('#skF_3','#skF_6',C_340)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_339,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_340,u1_struct_0('#skF_3'))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | r1_tarski(k3_orders_2('#skF_3',D_339,C_340),k3_orders_2('#skF_3','#skF_6',C_340))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_340),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3',D_339,C_340),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1063,c_253])).

tff(c_1075,plain,(
    ! [D_339,C_340] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_339,C_340),k3_orders_2('#skF_3','#skF_6',C_340)),'#skF_6')
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_339,C_340),k3_orders_2('#skF_3','#skF_6',C_340)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_339,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_340,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | r1_tarski(k3_orders_2('#skF_3',D_339,C_340),k3_orders_2('#skF_3','#skF_6',C_340))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_340),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3',D_339,C_340),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_1066])).

tff(c_1174,plain,(
    ! [D_366,C_367] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_366,C_367),k3_orders_2('#skF_3','#skF_6',C_367)),'#skF_6')
      | ~ m1_subset_1('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_366,C_367),k3_orders_2('#skF_3','#skF_6',C_367)),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_366,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_367,u1_struct_0('#skF_3'))
      | r1_tarski(k3_orders_2('#skF_3',D_366,C_367),k3_orders_2('#skF_3','#skF_6',C_367))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_367),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3',D_366,C_367),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1075])).

tff(c_18059,plain,(
    ! [D_1550,C_1551] :
      ( ~ r2_hidden('#skF_2'(u1_struct_0('#skF_3'),k3_orders_2('#skF_3',D_1550,C_1551),k3_orders_2('#skF_3','#skF_6',C_1551)),'#skF_6')
      | ~ m1_subset_1(D_1550,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_1551,u1_struct_0('#skF_3'))
      | r1_tarski(k3_orders_2('#skF_3',D_1550,C_1551),k3_orders_2('#skF_3','#skF_6',C_1551))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_1551),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3',D_1550,C_1551),k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_12,c_1174])).

tff(c_18107,plain,(
    ! [C_323] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ r1_tarski('#skF_5','#skF_6')
      | r1_tarski(k3_orders_2('#skF_3','#skF_5',C_323),k3_orders_2('#skF_3','#skF_6',C_323))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_323),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_323),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_323,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1019,c_18059])).

tff(c_18180,plain,(
    ! [C_1552] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_1552),k3_orders_2('#skF_3','#skF_6',C_1552))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_1552),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_5',C_1552),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_1552,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_18107])).

tff(c_18183,plain,(
    ! [C_15] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_15),k3_orders_2('#skF_3','#skF_6',C_15))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_15),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_18180])).

tff(c_18186,plain,(
    ! [C_15] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_15),k3_orders_2('#skF_3','#skF_6',C_15))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_15),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_18183])).

tff(c_18188,plain,(
    ! [C_1553] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_1553),k3_orders_2('#skF_3','#skF_6',C_1553))
      | ~ m1_subset_1(k3_orders_2('#skF_3','#skF_6',C_1553),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(C_1553,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18186])).

tff(c_18191,plain,(
    ! [C_15] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_15),k3_orders_2('#skF_3','#skF_6',C_15))
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_orders_2('#skF_3')
      | ~ v5_orders_2('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | ~ v3_orders_2('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_18188])).

tff(c_18194,plain,(
    ! [C_15] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_15),k3_orders_2('#skF_3','#skF_6',C_15))
      | ~ m1_subset_1(C_15,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_26,c_18191])).

tff(c_18196,plain,(
    ! [C_1554] :
      ( r1_tarski(k3_orders_2('#skF_3','#skF_5',C_1554),k3_orders_2('#skF_3','#skF_6',C_1554))
      | ~ m1_subset_1(C_1554,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_18194])).

tff(c_22,plain,(
    ~ r1_tarski(k3_orders_2('#skF_3','#skF_5','#skF_4'),k3_orders_2('#skF_3','#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_18273,plain,(
    ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_18196,c_22])).

tff(c_18322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_18273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.37/7.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/7.39  
% 15.37/7.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/7.39  %$ r2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 15.37/7.39  
% 15.37/7.39  %Foreground sorts:
% 15.37/7.39  
% 15.37/7.39  
% 15.37/7.39  %Background operators:
% 15.37/7.39  
% 15.37/7.39  
% 15.37/7.39  %Foreground operators:
% 15.37/7.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.37/7.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 15.37/7.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.37/7.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.37/7.39  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 15.37/7.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.37/7.39  tff('#skF_5', type, '#skF_5': $i).
% 15.37/7.39  tff('#skF_6', type, '#skF_6': $i).
% 15.37/7.39  tff('#skF_3', type, '#skF_3': $i).
% 15.37/7.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.37/7.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 15.37/7.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 15.37/7.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.37/7.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 15.37/7.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.37/7.39  tff('#skF_4', type, '#skF_4': $i).
% 15.37/7.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.37/7.39  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 15.37/7.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.37/7.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.37/7.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.37/7.39  
% 15.37/7.41  tff(f_114, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(C, D) => r1_tarski(k3_orders_2(A, C, B), k3_orders_2(A, D, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_orders_2)).
% 15.37/7.41  tff(f_63, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k3_orders_2(A, B, C), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_orders_2)).
% 15.37/7.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.37/7.41  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 15.37/7.41  tff(f_89, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 15.37/7.41  tff(c_30, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_40, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_38, plain, (v3_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_36, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_34, plain, (v5_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_32, plain, (l1_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_14, plain, (![A_13, B_14, C_15]: (m1_subset_1(k3_orders_2(A_13, B_14, C_15), k1_zfmisc_1(u1_struct_0(A_13))) | ~m1_subset_1(C_15, u1_struct_0(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_orders_2(A_13) | ~v5_orders_2(A_13) | ~v4_orders_2(A_13) | ~v3_orders_2(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.37/7.41  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.37/7.41  tff(c_42, plain, (![A_44, B_45]: (~r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.37/7.41  tff(c_47, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_42])).
% 15.37/7.41  tff(c_12, plain, (![A_6, B_7, C_11]: (m1_subset_1('#skF_2'(A_6, B_7, C_11), A_6) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.37/7.41  tff(c_100, plain, (![A_68, B_69, C_70]: (r2_hidden('#skF_2'(A_68, B_69, C_70), B_69) | r1_tarski(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.37/7.41  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.37/7.41  tff(c_103, plain, (![A_68, B_69, C_70, B_2]: (r2_hidden('#skF_2'(A_68, B_69, C_70), B_2) | ~r1_tarski(B_69, B_2) | r1_tarski(B_69, C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_100, c_2])).
% 15.37/7.41  tff(c_160, plain, (![B_102, D_103, A_104, C_105]: (r2_hidden(B_102, D_103) | ~r2_hidden(B_102, k3_orders_2(A_104, D_103, C_105)) | ~m1_subset_1(D_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(C_105, u1_struct_0(A_104)) | ~m1_subset_1(B_102, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v5_orders_2(A_104) | ~v4_orders_2(A_104) | ~v3_orders_2(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.37/7.41  tff(c_403, plain, (![A_190, C_185, B_189, A_187, C_188, D_186]: (r2_hidden('#skF_2'(A_190, B_189, C_188), D_186) | ~m1_subset_1(D_186, k1_zfmisc_1(u1_struct_0(A_187))) | ~m1_subset_1(C_185, u1_struct_0(A_187)) | ~m1_subset_1('#skF_2'(A_190, B_189, C_188), u1_struct_0(A_187)) | ~l1_orders_2(A_187) | ~v5_orders_2(A_187) | ~v4_orders_2(A_187) | ~v3_orders_2(A_187) | v2_struct_0(A_187) | ~r1_tarski(B_189, k3_orders_2(A_187, D_186, C_185)) | r1_tarski(B_189, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_189, k1_zfmisc_1(A_190)))), inference(resolution, [status(thm)], [c_103, c_160])).
% 15.37/7.41  tff(c_412, plain, (![A_190, B_189, C_188, C_185]: (r2_hidden('#skF_2'(A_190, B_189, C_188), '#skF_5') | ~m1_subset_1(C_185, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(A_190, B_189, C_188), u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~r1_tarski(B_189, k3_orders_2('#skF_3', '#skF_5', C_185)) | r1_tarski(B_189, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_189, k1_zfmisc_1(A_190)))), inference(resolution, [status(thm)], [c_28, c_403])).
% 15.37/7.41  tff(c_421, plain, (![A_190, B_189, C_188, C_185]: (r2_hidden('#skF_2'(A_190, B_189, C_188), '#skF_5') | ~m1_subset_1(C_185, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(A_190, B_189, C_188), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r1_tarski(B_189, k3_orders_2('#skF_3', '#skF_5', C_185)) | r1_tarski(B_189, C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(A_190)) | ~m1_subset_1(B_189, k1_zfmisc_1(A_190)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_412])).
% 15.37/7.41  tff(c_594, plain, (![A_237, B_238, C_239, C_240]: (r2_hidden('#skF_2'(A_237, B_238, C_239), '#skF_5') | ~m1_subset_1(C_240, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(A_237, B_238, C_239), u1_struct_0('#skF_3')) | ~r1_tarski(B_238, k3_orders_2('#skF_3', '#skF_5', C_240)) | r1_tarski(B_238, C_239) | ~m1_subset_1(C_239, k1_zfmisc_1(A_237)) | ~m1_subset_1(B_238, k1_zfmisc_1(A_237)))), inference(negUnitSimplification, [status(thm)], [c_40, c_421])).
% 15.37/7.41  tff(c_599, plain, (![B_241, C_242, C_243]: (r2_hidden('#skF_2'(u1_struct_0('#skF_3'), B_241, C_242), '#skF_5') | ~m1_subset_1(C_243, u1_struct_0('#skF_3')) | ~r1_tarski(B_241, k3_orders_2('#skF_3', '#skF_5', C_243)) | r1_tarski(B_241, C_242) | ~m1_subset_1(C_242, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_12, c_594])).
% 15.37/7.41  tff(c_617, plain, (![C_249, C_250]: (r2_hidden('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', '#skF_5', C_249), C_250), '#skF_5') | ~m1_subset_1(C_249, u1_struct_0('#skF_3')) | r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_249), C_250) | ~m1_subset_1(C_250, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_249), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_47, c_599])).
% 15.37/7.41  tff(c_8, plain, (![A_6, B_7, C_11]: (~r2_hidden('#skF_2'(A_6, B_7, C_11), C_11) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.37/7.41  tff(c_621, plain, (![C_249]: (~m1_subset_1(C_249, u1_struct_0('#skF_3')) | r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_249), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_249), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_617, c_8])).
% 15.37/7.41  tff(c_628, plain, (![C_251]: (~m1_subset_1(C_251, u1_struct_0('#skF_3')) | r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_251), '#skF_5') | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_251), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_621])).
% 15.37/7.41  tff(c_632, plain, (![C_15]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_15), '#skF_5') | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_628])).
% 15.37/7.41  tff(c_635, plain, (![C_15]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_15), '#skF_5') | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_632])).
% 15.37/7.41  tff(c_637, plain, (![C_252]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_252), '#skF_5') | ~m1_subset_1(C_252, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_635])).
% 15.37/7.41  tff(c_118, plain, (![A_78, B_79, C_80, B_81]: (r2_hidden('#skF_2'(A_78, B_79, C_80), B_81) | ~r1_tarski(B_79, B_81) | r1_tarski(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_100, c_2])).
% 15.37/7.41  tff(c_126, plain, (![B_2, C_80, B_81, B_79, A_78]: (r2_hidden('#skF_2'(A_78, B_79, C_80), B_2) | ~r1_tarski(B_81, B_2) | ~r1_tarski(B_79, B_81) | r1_tarski(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_118, c_2])).
% 15.37/7.41  tff(c_694, plain, (![A_264, B_265, C_266, C_267]: (r2_hidden('#skF_2'(A_264, B_265, C_266), '#skF_5') | ~r1_tarski(B_265, k3_orders_2('#skF_3', '#skF_5', C_267)) | r1_tarski(B_265, C_266) | ~m1_subset_1(C_266, k1_zfmisc_1(A_264)) | ~m1_subset_1(B_265, k1_zfmisc_1(A_264)) | ~m1_subset_1(C_267, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_637, c_126])).
% 15.37/7.41  tff(c_1011, plain, (![A_322, C_323, C_324]: (r2_hidden('#skF_2'(A_322, k3_orders_2('#skF_3', '#skF_5', C_323), C_324), '#skF_5') | r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_323), C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(A_322)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_323), k1_zfmisc_1(A_322)) | ~m1_subset_1(C_323, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_47, c_694])).
% 15.37/7.41  tff(c_1019, plain, (![A_322, C_323, C_324, B_2]: (r2_hidden('#skF_2'(A_322, k3_orders_2('#skF_3', '#skF_5', C_323), C_324), B_2) | ~r1_tarski('#skF_5', B_2) | r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_323), C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(A_322)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_323), k1_zfmisc_1(A_322)) | ~m1_subset_1(C_323, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1011, c_2])).
% 15.37/7.41  tff(c_10, plain, (![A_6, B_7, C_11]: (r2_hidden('#skF_2'(A_6, B_7, C_11), B_7) | r1_tarski(B_7, C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.37/7.41  tff(c_185, plain, (![A_106, B_107, C_108, D_109]: (r2_orders_2(A_106, B_107, C_108) | ~r2_hidden(B_107, k3_orders_2(A_106, D_109, C_108)) | ~m1_subset_1(D_109, k1_zfmisc_1(u1_struct_0(A_106))) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v5_orders_2(A_106) | ~v4_orders_2(A_106) | ~v3_orders_2(A_106) | v2_struct_0(A_106))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.37/7.41  tff(c_660, plain, (![D_256, A_255, A_257, C_253, C_254]: (r2_orders_2(A_257, '#skF_2'(A_255, k3_orders_2(A_257, D_256, C_253), C_254), C_253) | ~m1_subset_1(D_256, k1_zfmisc_1(u1_struct_0(A_257))) | ~m1_subset_1(C_253, u1_struct_0(A_257)) | ~m1_subset_1('#skF_2'(A_255, k3_orders_2(A_257, D_256, C_253), C_254), u1_struct_0(A_257)) | ~l1_orders_2(A_257) | ~v5_orders_2(A_257) | ~v4_orders_2(A_257) | ~v3_orders_2(A_257) | v2_struct_0(A_257) | r1_tarski(k3_orders_2(A_257, D_256, C_253), C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(A_255)) | ~m1_subset_1(k3_orders_2(A_257, D_256, C_253), k1_zfmisc_1(A_255)))), inference(resolution, [status(thm)], [c_10, c_185])).
% 15.37/7.41  tff(c_1063, plain, (![A_338, D_339, C_340, C_341]: (r2_orders_2(A_338, '#skF_2'(u1_struct_0(A_338), k3_orders_2(A_338, D_339, C_340), C_341), C_340) | ~m1_subset_1(D_339, k1_zfmisc_1(u1_struct_0(A_338))) | ~m1_subset_1(C_340, u1_struct_0(A_338)) | ~l1_orders_2(A_338) | ~v5_orders_2(A_338) | ~v4_orders_2(A_338) | ~v3_orders_2(A_338) | v2_struct_0(A_338) | r1_tarski(k3_orders_2(A_338, D_339, C_340), C_341) | ~m1_subset_1(C_341, k1_zfmisc_1(u1_struct_0(A_338))) | ~m1_subset_1(k3_orders_2(A_338, D_339, C_340), k1_zfmisc_1(u1_struct_0(A_338))))), inference(resolution, [status(thm)], [c_12, c_660])).
% 15.37/7.41  tff(c_210, plain, (![B_110, A_111, D_112, C_113]: (r2_hidden(B_110, k3_orders_2(A_111, D_112, C_113)) | ~r2_hidden(B_110, D_112) | ~r2_orders_2(A_111, B_110, C_113) | ~m1_subset_1(D_112, k1_zfmisc_1(u1_struct_0(A_111))) | ~m1_subset_1(C_113, u1_struct_0(A_111)) | ~m1_subset_1(B_110, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.37/7.41  tff(c_217, plain, (![B_110, C_113]: (r2_hidden(B_110, k3_orders_2('#skF_3', '#skF_6', C_113)) | ~r2_hidden(B_110, '#skF_6') | ~r2_orders_2('#skF_3', B_110, C_113) | ~m1_subset_1(C_113, u1_struct_0('#skF_3')) | ~m1_subset_1(B_110, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_210])).
% 15.37/7.41  tff(c_224, plain, (![B_110, C_113]: (r2_hidden(B_110, k3_orders_2('#skF_3', '#skF_6', C_113)) | ~r2_hidden(B_110, '#skF_6') | ~r2_orders_2('#skF_3', B_110, C_113) | ~m1_subset_1(C_113, u1_struct_0('#skF_3')) | ~m1_subset_1(B_110, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_217])).
% 15.37/7.41  tff(c_230, plain, (![B_114, C_115]: (r2_hidden(B_114, k3_orders_2('#skF_3', '#skF_6', C_115)) | ~r2_hidden(B_114, '#skF_6') | ~r2_orders_2('#skF_3', B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0('#skF_3')) | ~m1_subset_1(B_114, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_224])).
% 15.37/7.41  tff(c_253, plain, (![B_7, C_115, A_6]: (r1_tarski(B_7, k3_orders_2('#skF_3', '#skF_6', C_115)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_115), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)) | ~r2_hidden('#skF_2'(A_6, B_7, k3_orders_2('#skF_3', '#skF_6', C_115)), '#skF_6') | ~r2_orders_2('#skF_3', '#skF_2'(A_6, B_7, k3_orders_2('#skF_3', '#skF_6', C_115)), C_115) | ~m1_subset_1(C_115, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_2'(A_6, B_7, k3_orders_2('#skF_3', '#skF_6', C_115)), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_230, c_8])).
% 15.37/7.41  tff(c_1066, plain, (![D_339, C_340]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_339, C_340), k3_orders_2('#skF_3', '#skF_6', C_340)), '#skF_6') | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_339, C_340), k3_orders_2('#skF_3', '#skF_6', C_340)), u1_struct_0('#skF_3')) | ~m1_subset_1(D_339, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_340, u1_struct_0('#skF_3')) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3') | r1_tarski(k3_orders_2('#skF_3', D_339, C_340), k3_orders_2('#skF_3', '#skF_6', C_340)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_340), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', D_339, C_340), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_1063, c_253])).
% 15.37/7.41  tff(c_1075, plain, (![D_339, C_340]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_339, C_340), k3_orders_2('#skF_3', '#skF_6', C_340)), '#skF_6') | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_339, C_340), k3_orders_2('#skF_3', '#skF_6', C_340)), u1_struct_0('#skF_3')) | ~m1_subset_1(D_339, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_340, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | r1_tarski(k3_orders_2('#skF_3', D_339, C_340), k3_orders_2('#skF_3', '#skF_6', C_340)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_340), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', D_339, C_340), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_1066])).
% 15.37/7.41  tff(c_1174, plain, (![D_366, C_367]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_366, C_367), k3_orders_2('#skF_3', '#skF_6', C_367)), '#skF_6') | ~m1_subset_1('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_366, C_367), k3_orders_2('#skF_3', '#skF_6', C_367)), u1_struct_0('#skF_3')) | ~m1_subset_1(D_366, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_367, u1_struct_0('#skF_3')) | r1_tarski(k3_orders_2('#skF_3', D_366, C_367), k3_orders_2('#skF_3', '#skF_6', C_367)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_367), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', D_366, C_367), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_1075])).
% 15.37/7.41  tff(c_18059, plain, (![D_1550, C_1551]: (~r2_hidden('#skF_2'(u1_struct_0('#skF_3'), k3_orders_2('#skF_3', D_1550, C_1551), k3_orders_2('#skF_3', '#skF_6', C_1551)), '#skF_6') | ~m1_subset_1(D_1550, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_1551, u1_struct_0('#skF_3')) | r1_tarski(k3_orders_2('#skF_3', D_1550, C_1551), k3_orders_2('#skF_3', '#skF_6', C_1551)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_1551), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', D_1550, C_1551), k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_12, c_1174])).
% 15.37/7.41  tff(c_18107, plain, (![C_323]: (~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~r1_tarski('#skF_5', '#skF_6') | r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_323), k3_orders_2('#skF_3', '#skF_6', C_323)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_323), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_323), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_323, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1019, c_18059])).
% 15.37/7.41  tff(c_18180, plain, (![C_1552]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_1552), k3_orders_2('#skF_3', '#skF_6', C_1552)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_1552), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_5', C_1552), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_1552, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_18107])).
% 15.37/7.41  tff(c_18183, plain, (![C_15]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_15), k3_orders_2('#skF_3', '#skF_6', C_15)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_15), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_18180])).
% 15.37/7.41  tff(c_18186, plain, (![C_15]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_15), k3_orders_2('#skF_3', '#skF_6', C_15)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_15), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_18183])).
% 15.37/7.41  tff(c_18188, plain, (![C_1553]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_1553), k3_orders_2('#skF_3', '#skF_6', C_1553)) | ~m1_subset_1(k3_orders_2('#skF_3', '#skF_6', C_1553), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(C_1553, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_18186])).
% 15.37/7.41  tff(c_18191, plain, (![C_15]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_15), k3_orders_2('#skF_3', '#skF_6', C_15)) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_orders_2('#skF_3') | ~v5_orders_2('#skF_3') | ~v4_orders_2('#skF_3') | ~v3_orders_2('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_18188])).
% 15.37/7.41  tff(c_18194, plain, (![C_15]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_15), k3_orders_2('#skF_3', '#skF_6', C_15)) | ~m1_subset_1(C_15, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_26, c_18191])).
% 15.37/7.41  tff(c_18196, plain, (![C_1554]: (r1_tarski(k3_orders_2('#skF_3', '#skF_5', C_1554), k3_orders_2('#skF_3', '#skF_6', C_1554)) | ~m1_subset_1(C_1554, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_40, c_18194])).
% 15.37/7.41  tff(c_22, plain, (~r1_tarski(k3_orders_2('#skF_3', '#skF_5', '#skF_4'), k3_orders_2('#skF_3', '#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.37/7.41  tff(c_18273, plain, (~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_18196, c_22])).
% 15.37/7.41  tff(c_18322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_18273])).
% 15.37/7.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.37/7.41  
% 15.37/7.41  Inference rules
% 15.37/7.41  ----------------------
% 15.37/7.41  #Ref     : 0
% 15.37/7.41  #Sup     : 4511
% 15.37/7.41  #Fact    : 0
% 15.37/7.41  #Define  : 0
% 15.37/7.41  #Split   : 5
% 15.37/7.41  #Chain   : 0
% 15.37/7.42  #Close   : 0
% 15.37/7.42  
% 15.37/7.42  Ordering : KBO
% 15.37/7.42  
% 15.37/7.42  Simplification rules
% 15.37/7.42  ----------------------
% 15.37/7.42  #Subsume      : 2740
% 15.37/7.42  #Demod        : 1424
% 15.37/7.42  #Tautology    : 39
% 15.37/7.42  #SimpNegUnit  : 252
% 15.37/7.42  #BackRed      : 0
% 15.37/7.42  
% 15.37/7.42  #Partial instantiations: 0
% 15.37/7.42  #Strategies tried      : 1
% 15.37/7.42  
% 15.37/7.42  Timing (in seconds)
% 15.37/7.42  ----------------------
% 15.37/7.42  Preprocessing        : 0.29
% 15.37/7.42  Parsing              : 0.16
% 15.37/7.42  CNF conversion       : 0.02
% 15.37/7.42  Main loop            : 6.41
% 15.37/7.42  Inferencing          : 1.10
% 15.37/7.42  Reduction            : 1.08
% 15.37/7.42  Demodulation         : 0.72
% 15.37/7.42  BG Simplification    : 0.08
% 15.37/7.42  Subsumption          : 3.94
% 15.37/7.42  Abstraction          : 0.18
% 15.37/7.42  MUC search           : 0.00
% 15.37/7.42  Cooper               : 0.00
% 15.37/7.42  Total                : 6.74
% 15.37/7.42  Index Insertion      : 0.00
% 15.37/7.42  Index Deletion       : 0.00
% 15.37/7.42  Index Matching       : 0.00
% 15.37/7.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
