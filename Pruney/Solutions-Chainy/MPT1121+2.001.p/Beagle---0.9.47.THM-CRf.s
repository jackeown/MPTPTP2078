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
% DateTime   : Thu Dec  3 10:19:05 EST 2020

% Result     : Theorem 15.09s
% Output     : CNFRefutation 15.09s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 626 expanded)
%              Number of leaves         :   28 ( 225 expanded)
%              Depth                    :   18
%              Number of atoms          :  394 (2016 expanded)
%              Number of equality atoms :   16 ( 222 expanded)
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

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v4_pre_topc(B,A)
               => k2_pre_topc(A,B) = B )
              & ( ( v2_pre_topc(A)
                  & k2_pre_topc(A,B) = B )
               => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_107,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_pre_topc)).

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(B,k2_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_86,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_pre_topc)).

tff(c_60,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_63,plain,(
    v2_pre_topc('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_48,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    ! [A_42,B_50] :
      ( m1_subset_1('#skF_4'(A_42,B_50),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42))))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_65,plain,(
    k2_pre_topc('#skF_5','#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( k2_pre_topc('#skF_5','#skF_6') != '#skF_6'
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_71,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_50])).

tff(c_294,plain,(
    ! [A_114,B_115] :
      ( k6_setfam_1(u1_struct_0(A_114),'#skF_4'(A_114,B_115)) = k2_pre_topc(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_298,plain,
    ( k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')) = k2_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_294])).

tff(c_302,plain,(
    k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_65,c_298])).

tff(c_22,plain,(
    ! [A_14,B_18] :
      ( m1_subset_1('#skF_2'(A_14,B_18),k1_zfmisc_1(u1_struct_0(A_14)))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_14),B_18),A_14)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14))))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_405,plain,(
    ! [A_138,B_139] :
      ( ~ v4_pre_topc('#skF_2'(A_138,B_139),A_138)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_138),B_139),A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138))))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1089,plain,(
    ! [A_249,B_250] :
      ( ~ v4_pre_topc('#skF_2'(A_249,'#skF_4'(A_249,B_250)),A_249)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_249),'#skF_4'(A_249,B_250)),A_249)
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0(A_249)))
      | ~ l1_pre_topc(A_249)
      | ~ v2_pre_topc(A_249) ) ),
    inference(resolution,[status(thm)],[c_36,c_405])).

tff(c_1095,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_1089])).

tff(c_1097,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_1095])).

tff(c_1098,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1097])).

tff(c_503,plain,(
    ! [A_163,B_164] :
      ( r2_hidden('#skF_2'(A_163,B_164),B_164)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_163),B_164),A_163)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_163))))
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1844,plain,(
    ! [A_348,B_349] :
      ( r2_hidden('#skF_2'(A_348,'#skF_4'(A_348,B_349)),'#skF_4'(A_348,B_349))
      | v4_pre_topc(k6_setfam_1(u1_struct_0(A_348),'#skF_4'(A_348,B_349)),A_348)
      | ~ m1_subset_1(B_349,k1_zfmisc_1(u1_struct_0(A_348)))
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348) ) ),
    inference(resolution,[status(thm)],[c_36,c_503])).

tff(c_1856,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_1844])).

tff(c_1862,plain,
    ( r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_1856])).

tff(c_1863,plain,(
    r2_hidden('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_4'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1862])).

tff(c_42,plain,(
    ! [D_55,A_42,B_50] :
      ( v4_pre_topc(D_55,A_42)
      | ~ r2_hidden(D_55,'#skF_4'(A_42,B_50))
      | ~ m1_subset_1(D_55,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1865,plain,
    ( v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1863,c_42])).

tff(c_1874,plain,
    ( v4_pre_topc('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_1865])).

tff(c_1875,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'('#skF_5','#skF_6')),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_1874])).

tff(c_1883,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_5'),'#skF_4'('#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1875])).

tff(c_1886,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_302,c_1883])).

tff(c_1887,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1886])).

tff(c_1890,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1887])).

tff(c_1894,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_48,c_46,c_1890])).

tff(c_1896,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1934,plain,(
    ! [B_365,A_366] :
      ( r1_tarski(B_365,k2_pre_topc(A_366,B_365))
      | ~ m1_subset_1(B_365,k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ l1_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1936,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1934])).

tff(c_1939,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1936])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1941,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1939,c_8])).

tff(c_1944,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_1896,c_1941])).

tff(c_1895,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k2_pre_topc(A_12,B_13),k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1965,plain,(
    ! [A_372,B_373] :
      ( m1_subset_1(k2_pre_topc(A_372,B_373),k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_pre_topc(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_44,plain,(
    ! [B_58,A_56] :
      ( r1_tarski(B_58,k2_pre_topc(A_56,B_58))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1972,plain,(
    ! [A_372,B_373] :
      ( r1_tarski(k2_pre_topc(A_372,B_373),k2_pre_topc(A_372,k2_pre_topc(A_372,B_373)))
      | ~ m1_subset_1(B_373,k1_zfmisc_1(u1_struct_0(A_372)))
      | ~ l1_pre_topc(A_372) ) ),
    inference(resolution,[status(thm)],[c_1965,c_44])).

tff(c_2342,plain,(
    ! [A_425,B_426] :
      ( r1_tarski(k2_pre_topc(A_425,B_426),k2_pre_topc(A_425,k2_pre_topc(A_425,B_426)))
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ l1_pre_topc(A_425) ) ),
    inference(resolution,[status(thm)],[c_1965,c_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1914,plain,(
    ! [C_356,B_357,A_358] :
      ( r2_hidden(C_356,B_357)
      | ~ r2_hidden(C_356,A_358)
      | ~ r1_tarski(A_358,B_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1922,plain,(
    ! [A_362,B_363,B_364] :
      ( r2_hidden('#skF_1'(A_362,B_363),B_364)
      | ~ r1_tarski(A_362,B_364)
      | r1_tarski(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_6,c_1914])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1932,plain,(
    ! [A_362,B_363,B_2,B_364] :
      ( r2_hidden('#skF_1'(A_362,B_363),B_2)
      | ~ r1_tarski(B_364,B_2)
      | ~ r1_tarski(A_362,B_364)
      | r1_tarski(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_1922,c_2])).

tff(c_7155,plain,(
    ! [A_785,B_786,A_787,B_788] :
      ( r2_hidden('#skF_1'(A_785,B_786),k2_pre_topc(A_787,k2_pre_topc(A_787,B_788)))
      | ~ r1_tarski(A_785,k2_pre_topc(A_787,B_788))
      | r1_tarski(A_785,B_786)
      | ~ m1_subset_1(B_788,k1_zfmisc_1(u1_struct_0(A_787)))
      | ~ l1_pre_topc(A_787) ) ),
    inference(resolution,[status(thm)],[c_2342,c_1932])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_7170,plain,(
    ! [A_789,A_790,B_791] :
      ( ~ r1_tarski(A_789,k2_pre_topc(A_790,B_791))
      | r1_tarski(A_789,k2_pre_topc(A_790,k2_pre_topc(A_790,B_791)))
      | ~ m1_subset_1(B_791,k1_zfmisc_1(u1_struct_0(A_790)))
      | ~ l1_pre_topc(A_790) ) ),
    inference(resolution,[status(thm)],[c_7155,c_4])).

tff(c_1983,plain,(
    ! [A_378,B_379,B_380,B_381] :
      ( r2_hidden('#skF_1'(A_378,B_379),B_380)
      | ~ r1_tarski(B_381,B_380)
      | ~ r1_tarski(A_378,B_381)
      | r1_tarski(A_378,B_379) ) ),
    inference(resolution,[status(thm)],[c_1922,c_2])).

tff(c_2026,plain,(
    ! [A_386,B_387] :
      ( r2_hidden('#skF_1'(A_386,B_387),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_tarski(A_386,'#skF_6')
      | r1_tarski(A_386,B_387) ) ),
    inference(resolution,[status(thm)],[c_1939,c_1983])).

tff(c_2394,plain,(
    ! [A_436,B_437,B_438] :
      ( r2_hidden('#skF_1'(A_436,B_437),B_438)
      | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_438)
      | ~ r1_tarski(A_436,'#skF_6')
      | r1_tarski(A_436,B_437) ) ),
    inference(resolution,[status(thm)],[c_2026,c_2])).

tff(c_2405,plain,(
    ! [B_438,A_436] :
      ( ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_438)
      | ~ r1_tarski(A_436,'#skF_6')
      | r1_tarski(A_436,B_438) ) ),
    inference(resolution,[status(thm)],[c_2394,c_4])).

tff(c_7602,plain,(
    ! [A_826,A_827,B_828] :
      ( ~ r1_tarski(A_826,'#skF_6')
      | r1_tarski(A_826,k2_pre_topc(A_827,k2_pre_topc(A_827,B_828)))
      | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc(A_827,B_828))
      | ~ m1_subset_1(B_828,k1_zfmisc_1(u1_struct_0(A_827)))
      | ~ l1_pre_topc(A_827) ) ),
    inference(resolution,[status(thm)],[c_7170,c_2405])).

tff(c_7617,plain,(
    ! [A_826] :
      ( ~ r1_tarski(A_826,'#skF_6')
      | r1_tarski(A_826,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1972,c_7602])).

tff(c_7637,plain,(
    ! [A_826] :
      ( ~ r1_tarski(A_826,'#skF_6')
      | r1_tarski(A_826,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_7617])).

tff(c_7647,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_7637])).

tff(c_7663,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_7647])).

tff(c_7667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_7663])).

tff(c_7669,plain,(
    m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_7637])).

tff(c_7727,plain,
    ( r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_7669,c_44])).

tff(c_7775,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7727])).

tff(c_14,plain,(
    ! [C_11,A_8,B_9] :
      ( r2_hidden(C_11,A_8)
      | ~ r2_hidden(C_11,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2303,plain,(
    ! [A_416,B_417,A_418,B_419] :
      ( r2_hidden('#skF_1'(A_416,B_417),A_418)
      | ~ m1_subset_1(B_419,k1_zfmisc_1(A_418))
      | ~ r1_tarski(A_416,B_419)
      | r1_tarski(A_416,B_417) ) ),
    inference(resolution,[status(thm)],[c_1922,c_14])).

tff(c_2311,plain,(
    ! [A_416,B_417,A_12,B_13] :
      ( r2_hidden('#skF_1'(A_416,B_417),u1_struct_0(A_12))
      | ~ r1_tarski(A_416,k2_pre_topc(A_12,B_13))
      | r1_tarski(A_416,B_417)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_2303])).

tff(c_7879,plain,(
    ! [B_417] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_417),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_417)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7775,c_2311])).

tff(c_7928,plain,(
    ! [B_417] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_417),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_417) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_7669,c_7879])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_5115,plain,(
    ! [C_643,D_644,B_645,A_646] :
      ( r2_hidden(C_643,D_644)
      | ~ r1_tarski(B_645,D_644)
      | ~ v4_pre_topc(D_644,A_646)
      | ~ m1_subset_1(D_644,k1_zfmisc_1(u1_struct_0(A_646)))
      | ~ r2_hidden(C_643,k2_pre_topc(A_646,B_645))
      | ~ r2_hidden(C_643,u1_struct_0(A_646))
      | ~ m1_subset_1(B_645,k1_zfmisc_1(u1_struct_0(A_646)))
      | ~ l1_pre_topc(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5171,plain,(
    ! [C_649,B_650,A_651] :
      ( r2_hidden(C_649,B_650)
      | ~ v4_pre_topc(B_650,A_651)
      | ~ r2_hidden(C_649,k2_pre_topc(A_651,B_650))
      | ~ r2_hidden(C_649,u1_struct_0(A_651))
      | ~ m1_subset_1(B_650,k1_zfmisc_1(u1_struct_0(A_651)))
      | ~ l1_pre_topc(A_651) ) ),
    inference(resolution,[status(thm)],[c_12,c_5115])).

tff(c_14017,plain,(
    ! [A_1050,B_1051,B_1052] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_1050,B_1051),B_1052),B_1051)
      | ~ v4_pre_topc(B_1051,A_1050)
      | ~ r2_hidden('#skF_1'(k2_pre_topc(A_1050,B_1051),B_1052),u1_struct_0(A_1050))
      | ~ m1_subset_1(B_1051,k1_zfmisc_1(u1_struct_0(A_1050)))
      | ~ l1_pre_topc(A_1050)
      | r1_tarski(k2_pre_topc(A_1050,B_1051),B_1052) ) ),
    inference(resolution,[status(thm)],[c_6,c_5171])).

tff(c_14034,plain,(
    ! [B_417] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_417),'#skF_6')
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_417) ) ),
    inference(resolution,[status(thm)],[c_7928,c_14017])).

tff(c_14106,plain,(
    ! [B_1053] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1053),'#skF_6')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1053) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_1895,c_14034])).

tff(c_14114,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_14106,c_4])).

tff(c_14120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1944,c_1944,c_14114])).

tff(c_14122,plain,(
    ~ v2_pre_topc('#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k2_pre_topc('#skF_5','#skF_6') != '#skF_6'
    | v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_14123,plain,(
    k2_pre_topc('#skF_5','#skF_6') != '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_14122,c_58])).

tff(c_14163,plain,(
    ! [B_1069,A_1070] :
      ( r1_tarski(B_1069,k2_pre_topc(A_1070,B_1069))
      | ~ m1_subset_1(B_1069,k1_zfmisc_1(u1_struct_0(A_1070)))
      | ~ l1_pre_topc(A_1070) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_14165,plain,
    ( r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_14163])).

tff(c_14168,plain,(
    r1_tarski('#skF_6',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14165])).

tff(c_14170,plain,
    ( k2_pre_topc('#skF_5','#skF_6') = '#skF_6'
    | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_14168,c_8])).

tff(c_14173,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_14123,c_14170])).

tff(c_14121,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_14194,plain,(
    ! [A_1076,B_1077] :
      ( m1_subset_1(k2_pre_topc(A_1076,B_1077),k1_zfmisc_1(u1_struct_0(A_1076)))
      | ~ m1_subset_1(B_1077,k1_zfmisc_1(u1_struct_0(A_1076)))
      | ~ l1_pre_topc(A_1076) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14201,plain,(
    ! [A_1076,B_1077] :
      ( r1_tarski(k2_pre_topc(A_1076,B_1077),k2_pre_topc(A_1076,k2_pre_topc(A_1076,B_1077)))
      | ~ m1_subset_1(B_1077,k1_zfmisc_1(u1_struct_0(A_1076)))
      | ~ l1_pre_topc(A_1076) ) ),
    inference(resolution,[status(thm)],[c_14194,c_44])).

tff(c_14530,plain,(
    ! [A_1122,B_1123] :
      ( r1_tarski(k2_pre_topc(A_1122,B_1123),k2_pre_topc(A_1122,k2_pre_topc(A_1122,B_1123)))
      | ~ m1_subset_1(B_1123,k1_zfmisc_1(u1_struct_0(A_1122)))
      | ~ l1_pre_topc(A_1122) ) ),
    inference(resolution,[status(thm)],[c_14194,c_44])).

tff(c_14143,plain,(
    ! [C_1060,B_1061,A_1062] :
      ( r2_hidden(C_1060,B_1061)
      | ~ r2_hidden(C_1060,A_1062)
      | ~ r1_tarski(A_1062,B_1061) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14151,plain,(
    ! [A_1066,B_1067,B_1068] :
      ( r2_hidden('#skF_1'(A_1066,B_1067),B_1068)
      | ~ r1_tarski(A_1066,B_1068)
      | r1_tarski(A_1066,B_1067) ) ),
    inference(resolution,[status(thm)],[c_6,c_14143])).

tff(c_14161,plain,(
    ! [A_1066,B_1067,B_2,B_1068] :
      ( r2_hidden('#skF_1'(A_1066,B_1067),B_2)
      | ~ r1_tarski(B_1068,B_2)
      | ~ r1_tarski(A_1066,B_1068)
      | r1_tarski(A_1066,B_1067) ) ),
    inference(resolution,[status(thm)],[c_14151,c_2])).

tff(c_18629,plain,(
    ! [A_1475,B_1476,A_1477,B_1478] :
      ( r2_hidden('#skF_1'(A_1475,B_1476),k2_pre_topc(A_1477,k2_pre_topc(A_1477,B_1478)))
      | ~ r1_tarski(A_1475,k2_pre_topc(A_1477,B_1478))
      | r1_tarski(A_1475,B_1476)
      | ~ m1_subset_1(B_1478,k1_zfmisc_1(u1_struct_0(A_1477)))
      | ~ l1_pre_topc(A_1477) ) ),
    inference(resolution,[status(thm)],[c_14530,c_14161])).

tff(c_18644,plain,(
    ! [A_1479,A_1480,B_1481] :
      ( ~ r1_tarski(A_1479,k2_pre_topc(A_1480,B_1481))
      | r1_tarski(A_1479,k2_pre_topc(A_1480,k2_pre_topc(A_1480,B_1481)))
      | ~ m1_subset_1(B_1481,k1_zfmisc_1(u1_struct_0(A_1480)))
      | ~ l1_pre_topc(A_1480) ) ),
    inference(resolution,[status(thm)],[c_18629,c_4])).

tff(c_14212,plain,(
    ! [A_1082,B_1083,B_1084,B_1085] :
      ( r2_hidden('#skF_1'(A_1082,B_1083),B_1084)
      | ~ r1_tarski(B_1085,B_1084)
      | ~ r1_tarski(A_1082,B_1085)
      | r1_tarski(A_1082,B_1083) ) ),
    inference(resolution,[status(thm)],[c_14151,c_2])).

tff(c_14255,plain,(
    ! [A_1090,B_1091] :
      ( r2_hidden('#skF_1'(A_1090,B_1091),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r1_tarski(A_1090,'#skF_6')
      | r1_tarski(A_1090,B_1091) ) ),
    inference(resolution,[status(thm)],[c_14168,c_14212])).

tff(c_14585,plain,(
    ! [A_1132,B_1133,B_1134] :
      ( r2_hidden('#skF_1'(A_1132,B_1133),B_1134)
      | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1134)
      | ~ r1_tarski(A_1132,'#skF_6')
      | r1_tarski(A_1132,B_1133) ) ),
    inference(resolution,[status(thm)],[c_14255,c_2])).

tff(c_14596,plain,(
    ! [B_1134,A_1132] :
      ( ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1134)
      | ~ r1_tarski(A_1132,'#skF_6')
      | r1_tarski(A_1132,B_1134) ) ),
    inference(resolution,[status(thm)],[c_14585,c_4])).

tff(c_19440,plain,(
    ! [A_1516,A_1517,B_1518] :
      ( ~ r1_tarski(A_1516,'#skF_6')
      | r1_tarski(A_1516,k2_pre_topc(A_1517,k2_pre_topc(A_1517,B_1518)))
      | ~ r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc(A_1517,B_1518))
      | ~ m1_subset_1(B_1518,k1_zfmisc_1(u1_struct_0(A_1517)))
      | ~ l1_pre_topc(A_1517) ) ),
    inference(resolution,[status(thm)],[c_18644,c_14596])).

tff(c_19455,plain,(
    ! [A_1516] :
      ( ~ r1_tarski(A_1516,'#skF_6')
      | r1_tarski(A_1516,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14201,c_19440])).

tff(c_19475,plain,(
    ! [A_1516] :
      ( ~ r1_tarski(A_1516,'#skF_6')
      | r1_tarski(A_1516,k2_pre_topc('#skF_5',k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))))
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_19455])).

tff(c_19512,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_19475])).

tff(c_19515,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_19512])).

tff(c_19519,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_19515])).

tff(c_19521,plain,(
    m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_19475])).

tff(c_19576,plain,
    ( r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_19521,c_44])).

tff(c_19623,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),k2_pre_topc('#skF_5',k2_pre_topc('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_19576])).

tff(c_14462,plain,(
    ! [A_1110,B_1111,A_1112,B_1113] :
      ( r2_hidden('#skF_1'(A_1110,B_1111),A_1112)
      | ~ m1_subset_1(B_1113,k1_zfmisc_1(A_1112))
      | ~ r1_tarski(A_1110,B_1113)
      | r1_tarski(A_1110,B_1111) ) ),
    inference(resolution,[status(thm)],[c_14151,c_14])).

tff(c_14470,plain,(
    ! [A_1110,B_1111,A_12,B_13] :
      ( r2_hidden('#skF_1'(A_1110,B_1111),u1_struct_0(A_12))
      | ~ r1_tarski(A_1110,k2_pre_topc(A_12,B_13))
      | r1_tarski(A_1110,B_1111)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_12)))
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_14462])).

tff(c_19712,plain,(
    ! [B_1111] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1111),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1111)
      | ~ m1_subset_1(k2_pre_topc('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_19623,c_14470])).

tff(c_19761,plain,(
    ! [B_1111] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1111),u1_struct_0('#skF_5'))
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_19521,c_19712])).

tff(c_17162,plain,(
    ! [C_1355,D_1356,B_1357,A_1358] :
      ( r2_hidden(C_1355,D_1356)
      | ~ r1_tarski(B_1357,D_1356)
      | ~ v4_pre_topc(D_1356,A_1358)
      | ~ m1_subset_1(D_1356,k1_zfmisc_1(u1_struct_0(A_1358)))
      | ~ r2_hidden(C_1355,k2_pre_topc(A_1358,B_1357))
      | ~ r2_hidden(C_1355,u1_struct_0(A_1358))
      | ~ m1_subset_1(B_1357,k1_zfmisc_1(u1_struct_0(A_1358)))
      | ~ l1_pre_topc(A_1358) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_17240,plain,(
    ! [C_1367,B_1368,A_1369] :
      ( r2_hidden(C_1367,B_1368)
      | ~ v4_pre_topc(B_1368,A_1369)
      | ~ r2_hidden(C_1367,k2_pre_topc(A_1369,B_1368))
      | ~ r2_hidden(C_1367,u1_struct_0(A_1369))
      | ~ m1_subset_1(B_1368,k1_zfmisc_1(u1_struct_0(A_1369)))
      | ~ l1_pre_topc(A_1369) ) ),
    inference(resolution,[status(thm)],[c_12,c_17162])).

tff(c_28167,plain,(
    ! [A_1793,B_1794,B_1795] :
      ( r2_hidden('#skF_1'(k2_pre_topc(A_1793,B_1794),B_1795),B_1794)
      | ~ v4_pre_topc(B_1794,A_1793)
      | ~ r2_hidden('#skF_1'(k2_pre_topc(A_1793,B_1794),B_1795),u1_struct_0(A_1793))
      | ~ m1_subset_1(B_1794,k1_zfmisc_1(u1_struct_0(A_1793)))
      | ~ l1_pre_topc(A_1793)
      | r1_tarski(k2_pre_topc(A_1793,B_1794),B_1795) ) ),
    inference(resolution,[status(thm)],[c_6,c_17240])).

tff(c_28189,plain,(
    ! [B_1111] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1111),'#skF_6')
      | ~ v4_pre_topc('#skF_6','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1111) ) ),
    inference(resolution,[status(thm)],[c_19761,c_28167])).

tff(c_28267,plain,(
    ! [B_1796] :
      ( r2_hidden('#skF_1'(k2_pre_topc('#skF_5','#skF_6'),B_1796),'#skF_6')
      | r1_tarski(k2_pre_topc('#skF_5','#skF_6'),B_1796) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_14121,c_28189])).

tff(c_28275,plain,(
    r1_tarski(k2_pre_topc('#skF_5','#skF_6'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_28267,c_4])).

tff(c_28281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14173,c_14173,c_28275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.09/7.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.09/7.10  
% 15.09/7.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.09/7.11  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k6_setfam_1 > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 15.09/7.11  
% 15.09/7.11  %Foreground sorts:
% 15.09/7.11  
% 15.09/7.11  
% 15.09/7.11  %Background operators:
% 15.09/7.11  
% 15.09/7.11  
% 15.09/7.11  %Foreground operators:
% 15.09/7.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.09/7.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.09/7.11  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 15.09/7.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.09/7.11  tff('#skF_5', type, '#skF_5': $i).
% 15.09/7.11  tff('#skF_6', type, '#skF_6': $i).
% 15.09/7.11  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.09/7.11  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 15.09/7.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.09/7.11  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 15.09/7.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 15.09/7.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.09/7.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.09/7.11  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 15.09/7.11  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.09/7.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.09/7.11  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 15.09/7.11  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.09/7.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.09/7.11  
% 15.09/7.13  tff(f_130, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 15.09/7.13  tff(f_107, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (?[C]: ((m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> (v4_pre_topc(D, A) & r1_tarski(B, D)))))) & (k2_pre_topc(A, B) = k6_setfam_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_pre_topc)).
% 15.09/7.13  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, B) => v4_pre_topc(C, A)))) => v4_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_pre_topc)).
% 15.09/7.13  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(B, k2_pre_topc(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_pre_topc)).
% 15.09/7.13  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.09/7.13  tff(f_51, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 15.09/7.13  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.09/7.13  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 15.09/7.13  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (r2_hidden(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(D, A) & r1_tarski(B, D)) => r2_hidden(C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_pre_topc)).
% 15.09/7.13  tff(c_60, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.09/7.13  tff(c_63, plain, (v2_pre_topc('#skF_5')), inference(splitLeft, [status(thm)], [c_60])).
% 15.09/7.13  tff(c_48, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.09/7.13  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.09/7.13  tff(c_36, plain, (![A_42, B_50]: (m1_subset_1('#skF_4'(A_42, B_50), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_42)))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.09/7.13  tff(c_56, plain, (v4_pre_topc('#skF_6', '#skF_5') | k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.09/7.13  tff(c_65, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_56])).
% 15.09/7.13  tff(c_50, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6' | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.09/7.13  tff(c_71, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_50])).
% 15.09/7.13  tff(c_294, plain, (![A_114, B_115]: (k6_setfam_1(u1_struct_0(A_114), '#skF_4'(A_114, B_115))=k2_pre_topc(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.09/7.13  tff(c_298, plain, (k6_setfam_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6'))=k2_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_294])).
% 15.09/7.13  tff(c_302, plain, (k6_setfam_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_65, c_298])).
% 15.09/7.13  tff(c_22, plain, (![A_14, B_18]: (m1_subset_1('#skF_2'(A_14, B_18), k1_zfmisc_1(u1_struct_0(A_14))) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_14), B_18), A_14) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_14)))) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.09/7.13  tff(c_405, plain, (![A_138, B_139]: (~v4_pre_topc('#skF_2'(A_138, B_139), A_138) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_138), B_139), A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_138)))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.09/7.13  tff(c_1089, plain, (![A_249, B_250]: (~v4_pre_topc('#skF_2'(A_249, '#skF_4'(A_249, B_250)), A_249) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_249), '#skF_4'(A_249, B_250)), A_249) | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0(A_249))) | ~l1_pre_topc(A_249) | ~v2_pre_topc(A_249))), inference(resolution, [status(thm)], [c_36, c_405])).
% 15.09/7.13  tff(c_1095, plain, (~v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_302, c_1089])).
% 15.09/7.13  tff(c_1097, plain, (~v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_1095])).
% 15.09/7.13  tff(c_1098, plain, (~v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_71, c_1097])).
% 15.09/7.13  tff(c_503, plain, (![A_163, B_164]: (r2_hidden('#skF_2'(A_163, B_164), B_164) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_163), B_164), A_163) | ~m1_subset_1(B_164, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_163)))) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.09/7.13  tff(c_1844, plain, (![A_348, B_349]: (r2_hidden('#skF_2'(A_348, '#skF_4'(A_348, B_349)), '#skF_4'(A_348, B_349)) | v4_pre_topc(k6_setfam_1(u1_struct_0(A_348), '#skF_4'(A_348, B_349)), A_348) | ~m1_subset_1(B_349, k1_zfmisc_1(u1_struct_0(A_348))) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348))), inference(resolution, [status(thm)], [c_36, c_503])).
% 15.09/7.13  tff(c_1856, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_4'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_302, c_1844])).
% 15.09/7.13  tff(c_1862, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_4'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_1856])).
% 15.09/7.13  tff(c_1863, plain, (r2_hidden('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_4'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_71, c_1862])).
% 15.09/7.13  tff(c_42, plain, (![D_55, A_42, B_50]: (v4_pre_topc(D_55, A_42) | ~r2_hidden(D_55, '#skF_4'(A_42, B_50)) | ~m1_subset_1(D_55, k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_107])).
% 15.09/7.13  tff(c_1865, plain, (v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1863, c_42])).
% 15.09/7.13  tff(c_1874, plain, (v4_pre_topc('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_1865])).
% 15.09/7.13  tff(c_1875, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'('#skF_5', '#skF_6')), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_1098, c_1874])).
% 15.09/7.13  tff(c_1883, plain, (v4_pre_topc(k6_setfam_1(u1_struct_0('#skF_5'), '#skF_4'('#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1875])).
% 15.09/7.13  tff(c_1886, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_302, c_1883])).
% 15.09/7.13  tff(c_1887, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_71, c_1886])).
% 15.09/7.13  tff(c_1890, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_36, c_1887])).
% 15.09/7.13  tff(c_1894, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_48, c_46, c_1890])).
% 15.09/7.13  tff(c_1896, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_56])).
% 15.09/7.13  tff(c_1934, plain, (![B_365, A_366]: (r1_tarski(B_365, k2_pre_topc(A_366, B_365)) | ~m1_subset_1(B_365, k1_zfmisc_1(u1_struct_0(A_366))) | ~l1_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.09/7.13  tff(c_1936, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1934])).
% 15.09/7.13  tff(c_1939, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1936])).
% 15.09/7.13  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.09/7.13  tff(c_1941, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_1939, c_8])).
% 15.09/7.13  tff(c_1944, plain, (~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_1896, c_1941])).
% 15.09/7.13  tff(c_1895, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_56])).
% 15.09/7.13  tff(c_16, plain, (![A_12, B_13]: (m1_subset_1(k2_pre_topc(A_12, B_13), k1_zfmisc_1(u1_struct_0(A_12))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.09/7.13  tff(c_1965, plain, (![A_372, B_373]: (m1_subset_1(k2_pre_topc(A_372, B_373), k1_zfmisc_1(u1_struct_0(A_372))) | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0(A_372))) | ~l1_pre_topc(A_372))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.09/7.13  tff(c_44, plain, (![B_58, A_56]: (r1_tarski(B_58, k2_pre_topc(A_56, B_58)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.09/7.13  tff(c_1972, plain, (![A_372, B_373]: (r1_tarski(k2_pre_topc(A_372, B_373), k2_pre_topc(A_372, k2_pre_topc(A_372, B_373))) | ~m1_subset_1(B_373, k1_zfmisc_1(u1_struct_0(A_372))) | ~l1_pre_topc(A_372))), inference(resolution, [status(thm)], [c_1965, c_44])).
% 15.09/7.13  tff(c_2342, plain, (![A_425, B_426]: (r1_tarski(k2_pre_topc(A_425, B_426), k2_pre_topc(A_425, k2_pre_topc(A_425, B_426))) | ~m1_subset_1(B_426, k1_zfmisc_1(u1_struct_0(A_425))) | ~l1_pre_topc(A_425))), inference(resolution, [status(thm)], [c_1965, c_44])).
% 15.09/7.13  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.09/7.13  tff(c_1914, plain, (![C_356, B_357, A_358]: (r2_hidden(C_356, B_357) | ~r2_hidden(C_356, A_358) | ~r1_tarski(A_358, B_357))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.09/7.13  tff(c_1922, plain, (![A_362, B_363, B_364]: (r2_hidden('#skF_1'(A_362, B_363), B_364) | ~r1_tarski(A_362, B_364) | r1_tarski(A_362, B_363))), inference(resolution, [status(thm)], [c_6, c_1914])).
% 15.09/7.13  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.09/7.13  tff(c_1932, plain, (![A_362, B_363, B_2, B_364]: (r2_hidden('#skF_1'(A_362, B_363), B_2) | ~r1_tarski(B_364, B_2) | ~r1_tarski(A_362, B_364) | r1_tarski(A_362, B_363))), inference(resolution, [status(thm)], [c_1922, c_2])).
% 15.09/7.13  tff(c_7155, plain, (![A_785, B_786, A_787, B_788]: (r2_hidden('#skF_1'(A_785, B_786), k2_pre_topc(A_787, k2_pre_topc(A_787, B_788))) | ~r1_tarski(A_785, k2_pre_topc(A_787, B_788)) | r1_tarski(A_785, B_786) | ~m1_subset_1(B_788, k1_zfmisc_1(u1_struct_0(A_787))) | ~l1_pre_topc(A_787))), inference(resolution, [status(thm)], [c_2342, c_1932])).
% 15.09/7.13  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.09/7.13  tff(c_7170, plain, (![A_789, A_790, B_791]: (~r1_tarski(A_789, k2_pre_topc(A_790, B_791)) | r1_tarski(A_789, k2_pre_topc(A_790, k2_pre_topc(A_790, B_791))) | ~m1_subset_1(B_791, k1_zfmisc_1(u1_struct_0(A_790))) | ~l1_pre_topc(A_790))), inference(resolution, [status(thm)], [c_7155, c_4])).
% 15.09/7.13  tff(c_1983, plain, (![A_378, B_379, B_380, B_381]: (r2_hidden('#skF_1'(A_378, B_379), B_380) | ~r1_tarski(B_381, B_380) | ~r1_tarski(A_378, B_381) | r1_tarski(A_378, B_379))), inference(resolution, [status(thm)], [c_1922, c_2])).
% 15.09/7.13  tff(c_2026, plain, (![A_386, B_387]: (r2_hidden('#skF_1'(A_386, B_387), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_tarski(A_386, '#skF_6') | r1_tarski(A_386, B_387))), inference(resolution, [status(thm)], [c_1939, c_1983])).
% 15.09/7.13  tff(c_2394, plain, (![A_436, B_437, B_438]: (r2_hidden('#skF_1'(A_436, B_437), B_438) | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_438) | ~r1_tarski(A_436, '#skF_6') | r1_tarski(A_436, B_437))), inference(resolution, [status(thm)], [c_2026, c_2])).
% 15.09/7.13  tff(c_2405, plain, (![B_438, A_436]: (~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_438) | ~r1_tarski(A_436, '#skF_6') | r1_tarski(A_436, B_438))), inference(resolution, [status(thm)], [c_2394, c_4])).
% 15.09/7.13  tff(c_7602, plain, (![A_826, A_827, B_828]: (~r1_tarski(A_826, '#skF_6') | r1_tarski(A_826, k2_pre_topc(A_827, k2_pre_topc(A_827, B_828))) | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), k2_pre_topc(A_827, B_828)) | ~m1_subset_1(B_828, k1_zfmisc_1(u1_struct_0(A_827))) | ~l1_pre_topc(A_827))), inference(resolution, [status(thm)], [c_7170, c_2405])).
% 15.09/7.13  tff(c_7617, plain, (![A_826]: (~r1_tarski(A_826, '#skF_6') | r1_tarski(A_826, k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6')))) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1972, c_7602])).
% 15.09/7.13  tff(c_7637, plain, (![A_826]: (~r1_tarski(A_826, '#skF_6') | r1_tarski(A_826, k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6')))) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_7617])).
% 15.09/7.13  tff(c_7647, plain, (~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_7637])).
% 15.09/7.13  tff(c_7663, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_7647])).
% 15.09/7.13  tff(c_7667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_7663])).
% 15.09/7.13  tff(c_7669, plain, (m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_7637])).
% 15.09/7.13  tff(c_7727, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_7669, c_44])).
% 15.09/7.13  tff(c_7775, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7727])).
% 15.09/7.13  tff(c_14, plain, (![C_11, A_8, B_9]: (r2_hidden(C_11, A_8) | ~r2_hidden(C_11, B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.09/7.13  tff(c_2303, plain, (![A_416, B_417, A_418, B_419]: (r2_hidden('#skF_1'(A_416, B_417), A_418) | ~m1_subset_1(B_419, k1_zfmisc_1(A_418)) | ~r1_tarski(A_416, B_419) | r1_tarski(A_416, B_417))), inference(resolution, [status(thm)], [c_1922, c_14])).
% 15.09/7.13  tff(c_2311, plain, (![A_416, B_417, A_12, B_13]: (r2_hidden('#skF_1'(A_416, B_417), u1_struct_0(A_12)) | ~r1_tarski(A_416, k2_pre_topc(A_12, B_13)) | r1_tarski(A_416, B_417) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_2303])).
% 15.09/7.13  tff(c_7879, plain, (![B_417]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_417), u1_struct_0('#skF_5')) | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_417) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_7775, c_2311])).
% 15.09/7.13  tff(c_7928, plain, (![B_417]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_417), u1_struct_0('#skF_5')) | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_417))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_7669, c_7879])).
% 15.09/7.13  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.09/7.13  tff(c_5115, plain, (![C_643, D_644, B_645, A_646]: (r2_hidden(C_643, D_644) | ~r1_tarski(B_645, D_644) | ~v4_pre_topc(D_644, A_646) | ~m1_subset_1(D_644, k1_zfmisc_1(u1_struct_0(A_646))) | ~r2_hidden(C_643, k2_pre_topc(A_646, B_645)) | ~r2_hidden(C_643, u1_struct_0(A_646)) | ~m1_subset_1(B_645, k1_zfmisc_1(u1_struct_0(A_646))) | ~l1_pre_topc(A_646))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.09/7.13  tff(c_5171, plain, (![C_649, B_650, A_651]: (r2_hidden(C_649, B_650) | ~v4_pre_topc(B_650, A_651) | ~r2_hidden(C_649, k2_pre_topc(A_651, B_650)) | ~r2_hidden(C_649, u1_struct_0(A_651)) | ~m1_subset_1(B_650, k1_zfmisc_1(u1_struct_0(A_651))) | ~l1_pre_topc(A_651))), inference(resolution, [status(thm)], [c_12, c_5115])).
% 15.09/7.13  tff(c_14017, plain, (![A_1050, B_1051, B_1052]: (r2_hidden('#skF_1'(k2_pre_topc(A_1050, B_1051), B_1052), B_1051) | ~v4_pre_topc(B_1051, A_1050) | ~r2_hidden('#skF_1'(k2_pre_topc(A_1050, B_1051), B_1052), u1_struct_0(A_1050)) | ~m1_subset_1(B_1051, k1_zfmisc_1(u1_struct_0(A_1050))) | ~l1_pre_topc(A_1050) | r1_tarski(k2_pre_topc(A_1050, B_1051), B_1052))), inference(resolution, [status(thm)], [c_6, c_5171])).
% 15.09/7.13  tff(c_14034, plain, (![B_417]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_417), '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_417))), inference(resolution, [status(thm)], [c_7928, c_14017])).
% 15.09/7.13  tff(c_14106, plain, (![B_1053]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_1053), '#skF_6') | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1053))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_1895, c_14034])).
% 15.09/7.13  tff(c_14114, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_14106, c_4])).
% 15.09/7.13  tff(c_14120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1944, c_1944, c_14114])).
% 15.09/7.13  tff(c_14122, plain, (~v2_pre_topc('#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 15.09/7.13  tff(c_58, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6' | v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.09/7.13  tff(c_14123, plain, (k2_pre_topc('#skF_5', '#skF_6')!='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_14122, c_58])).
% 15.09/7.13  tff(c_14163, plain, (![B_1069, A_1070]: (r1_tarski(B_1069, k2_pre_topc(A_1070, B_1069)) | ~m1_subset_1(B_1069, k1_zfmisc_1(u1_struct_0(A_1070))) | ~l1_pre_topc(A_1070))), inference(cnfTransformation, [status(thm)], [f_114])).
% 15.09/7.13  tff(c_14165, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_46, c_14163])).
% 15.09/7.13  tff(c_14168, plain, (r1_tarski('#skF_6', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14165])).
% 15.09/7.13  tff(c_14170, plain, (k2_pre_topc('#skF_5', '#skF_6')='#skF_6' | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_14168, c_8])).
% 15.09/7.13  tff(c_14173, plain, (~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_14123, c_14170])).
% 15.09/7.13  tff(c_14121, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_60])).
% 15.09/7.13  tff(c_14194, plain, (![A_1076, B_1077]: (m1_subset_1(k2_pre_topc(A_1076, B_1077), k1_zfmisc_1(u1_struct_0(A_1076))) | ~m1_subset_1(B_1077, k1_zfmisc_1(u1_struct_0(A_1076))) | ~l1_pre_topc(A_1076))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.09/7.13  tff(c_14201, plain, (![A_1076, B_1077]: (r1_tarski(k2_pre_topc(A_1076, B_1077), k2_pre_topc(A_1076, k2_pre_topc(A_1076, B_1077))) | ~m1_subset_1(B_1077, k1_zfmisc_1(u1_struct_0(A_1076))) | ~l1_pre_topc(A_1076))), inference(resolution, [status(thm)], [c_14194, c_44])).
% 15.09/7.13  tff(c_14530, plain, (![A_1122, B_1123]: (r1_tarski(k2_pre_topc(A_1122, B_1123), k2_pre_topc(A_1122, k2_pre_topc(A_1122, B_1123))) | ~m1_subset_1(B_1123, k1_zfmisc_1(u1_struct_0(A_1122))) | ~l1_pre_topc(A_1122))), inference(resolution, [status(thm)], [c_14194, c_44])).
% 15.09/7.13  tff(c_14143, plain, (![C_1060, B_1061, A_1062]: (r2_hidden(C_1060, B_1061) | ~r2_hidden(C_1060, A_1062) | ~r1_tarski(A_1062, B_1061))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.09/7.13  tff(c_14151, plain, (![A_1066, B_1067, B_1068]: (r2_hidden('#skF_1'(A_1066, B_1067), B_1068) | ~r1_tarski(A_1066, B_1068) | r1_tarski(A_1066, B_1067))), inference(resolution, [status(thm)], [c_6, c_14143])).
% 15.09/7.13  tff(c_14161, plain, (![A_1066, B_1067, B_2, B_1068]: (r2_hidden('#skF_1'(A_1066, B_1067), B_2) | ~r1_tarski(B_1068, B_2) | ~r1_tarski(A_1066, B_1068) | r1_tarski(A_1066, B_1067))), inference(resolution, [status(thm)], [c_14151, c_2])).
% 15.09/7.13  tff(c_18629, plain, (![A_1475, B_1476, A_1477, B_1478]: (r2_hidden('#skF_1'(A_1475, B_1476), k2_pre_topc(A_1477, k2_pre_topc(A_1477, B_1478))) | ~r1_tarski(A_1475, k2_pre_topc(A_1477, B_1478)) | r1_tarski(A_1475, B_1476) | ~m1_subset_1(B_1478, k1_zfmisc_1(u1_struct_0(A_1477))) | ~l1_pre_topc(A_1477))), inference(resolution, [status(thm)], [c_14530, c_14161])).
% 15.09/7.13  tff(c_18644, plain, (![A_1479, A_1480, B_1481]: (~r1_tarski(A_1479, k2_pre_topc(A_1480, B_1481)) | r1_tarski(A_1479, k2_pre_topc(A_1480, k2_pre_topc(A_1480, B_1481))) | ~m1_subset_1(B_1481, k1_zfmisc_1(u1_struct_0(A_1480))) | ~l1_pre_topc(A_1480))), inference(resolution, [status(thm)], [c_18629, c_4])).
% 15.09/7.13  tff(c_14212, plain, (![A_1082, B_1083, B_1084, B_1085]: (r2_hidden('#skF_1'(A_1082, B_1083), B_1084) | ~r1_tarski(B_1085, B_1084) | ~r1_tarski(A_1082, B_1085) | r1_tarski(A_1082, B_1083))), inference(resolution, [status(thm)], [c_14151, c_2])).
% 15.09/7.13  tff(c_14255, plain, (![A_1090, B_1091]: (r2_hidden('#skF_1'(A_1090, B_1091), k2_pre_topc('#skF_5', '#skF_6')) | ~r1_tarski(A_1090, '#skF_6') | r1_tarski(A_1090, B_1091))), inference(resolution, [status(thm)], [c_14168, c_14212])).
% 15.09/7.13  tff(c_14585, plain, (![A_1132, B_1133, B_1134]: (r2_hidden('#skF_1'(A_1132, B_1133), B_1134) | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1134) | ~r1_tarski(A_1132, '#skF_6') | r1_tarski(A_1132, B_1133))), inference(resolution, [status(thm)], [c_14255, c_2])).
% 15.09/7.13  tff(c_14596, plain, (![B_1134, A_1132]: (~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1134) | ~r1_tarski(A_1132, '#skF_6') | r1_tarski(A_1132, B_1134))), inference(resolution, [status(thm)], [c_14585, c_4])).
% 15.09/7.13  tff(c_19440, plain, (![A_1516, A_1517, B_1518]: (~r1_tarski(A_1516, '#skF_6') | r1_tarski(A_1516, k2_pre_topc(A_1517, k2_pre_topc(A_1517, B_1518))) | ~r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), k2_pre_topc(A_1517, B_1518)) | ~m1_subset_1(B_1518, k1_zfmisc_1(u1_struct_0(A_1517))) | ~l1_pre_topc(A_1517))), inference(resolution, [status(thm)], [c_18644, c_14596])).
% 15.09/7.13  tff(c_19455, plain, (![A_1516]: (~r1_tarski(A_1516, '#skF_6') | r1_tarski(A_1516, k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6')))) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_14201, c_19440])).
% 15.09/7.13  tff(c_19475, plain, (![A_1516]: (~r1_tarski(A_1516, '#skF_6') | r1_tarski(A_1516, k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6')))) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_19455])).
% 15.09/7.13  tff(c_19512, plain, (~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_19475])).
% 15.09/7.13  tff(c_19515, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_16, c_19512])).
% 15.09/7.13  tff(c_19519, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_19515])).
% 15.09/7.13  tff(c_19521, plain, (m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_19475])).
% 15.09/7.13  tff(c_19576, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6'))) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_19521, c_44])).
% 15.09/7.13  tff(c_19623, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), k2_pre_topc('#skF_5', k2_pre_topc('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_19576])).
% 15.09/7.13  tff(c_14462, plain, (![A_1110, B_1111, A_1112, B_1113]: (r2_hidden('#skF_1'(A_1110, B_1111), A_1112) | ~m1_subset_1(B_1113, k1_zfmisc_1(A_1112)) | ~r1_tarski(A_1110, B_1113) | r1_tarski(A_1110, B_1111))), inference(resolution, [status(thm)], [c_14151, c_14])).
% 15.09/7.13  tff(c_14470, plain, (![A_1110, B_1111, A_12, B_13]: (r2_hidden('#skF_1'(A_1110, B_1111), u1_struct_0(A_12)) | ~r1_tarski(A_1110, k2_pre_topc(A_12, B_13)) | r1_tarski(A_1110, B_1111) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_12))) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_14462])).
% 15.09/7.13  tff(c_19712, plain, (![B_1111]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_1111), u1_struct_0('#skF_5')) | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1111) | ~m1_subset_1(k2_pre_topc('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_19623, c_14470])).
% 15.09/7.13  tff(c_19761, plain, (![B_1111]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_1111), u1_struct_0('#skF_5')) | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1111))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_19521, c_19712])).
% 15.09/7.13  tff(c_17162, plain, (![C_1355, D_1356, B_1357, A_1358]: (r2_hidden(C_1355, D_1356) | ~r1_tarski(B_1357, D_1356) | ~v4_pre_topc(D_1356, A_1358) | ~m1_subset_1(D_1356, k1_zfmisc_1(u1_struct_0(A_1358))) | ~r2_hidden(C_1355, k2_pre_topc(A_1358, B_1357)) | ~r2_hidden(C_1355, u1_struct_0(A_1358)) | ~m1_subset_1(B_1357, k1_zfmisc_1(u1_struct_0(A_1358))) | ~l1_pre_topc(A_1358))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.09/7.13  tff(c_17240, plain, (![C_1367, B_1368, A_1369]: (r2_hidden(C_1367, B_1368) | ~v4_pre_topc(B_1368, A_1369) | ~r2_hidden(C_1367, k2_pre_topc(A_1369, B_1368)) | ~r2_hidden(C_1367, u1_struct_0(A_1369)) | ~m1_subset_1(B_1368, k1_zfmisc_1(u1_struct_0(A_1369))) | ~l1_pre_topc(A_1369))), inference(resolution, [status(thm)], [c_12, c_17162])).
% 15.09/7.13  tff(c_28167, plain, (![A_1793, B_1794, B_1795]: (r2_hidden('#skF_1'(k2_pre_topc(A_1793, B_1794), B_1795), B_1794) | ~v4_pre_topc(B_1794, A_1793) | ~r2_hidden('#skF_1'(k2_pre_topc(A_1793, B_1794), B_1795), u1_struct_0(A_1793)) | ~m1_subset_1(B_1794, k1_zfmisc_1(u1_struct_0(A_1793))) | ~l1_pre_topc(A_1793) | r1_tarski(k2_pre_topc(A_1793, B_1794), B_1795))), inference(resolution, [status(thm)], [c_6, c_17240])).
% 15.09/7.13  tff(c_28189, plain, (![B_1111]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_1111), '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1111))), inference(resolution, [status(thm)], [c_19761, c_28167])).
% 15.09/7.13  tff(c_28267, plain, (![B_1796]: (r2_hidden('#skF_1'(k2_pre_topc('#skF_5', '#skF_6'), B_1796), '#skF_6') | r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), B_1796))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_14121, c_28189])).
% 15.09/7.13  tff(c_28275, plain, (r1_tarski(k2_pre_topc('#skF_5', '#skF_6'), '#skF_6')), inference(resolution, [status(thm)], [c_28267, c_4])).
% 15.09/7.13  tff(c_28281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14173, c_14173, c_28275])).
% 15.09/7.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.09/7.13  
% 15.09/7.13  Inference rules
% 15.09/7.13  ----------------------
% 15.09/7.13  #Ref     : 0
% 15.09/7.13  #Sup     : 7000
% 15.09/7.13  #Fact    : 0
% 15.09/7.13  #Define  : 0
% 15.09/7.13  #Split   : 65
% 15.09/7.13  #Chain   : 0
% 15.09/7.13  #Close   : 0
% 15.09/7.13  
% 15.09/7.13  Ordering : KBO
% 15.09/7.13  
% 15.09/7.13  Simplification rules
% 15.09/7.13  ----------------------
% 15.09/7.13  #Subsume      : 4007
% 15.09/7.13  #Demod        : 2086
% 15.09/7.13  #Tautology    : 226
% 15.09/7.13  #SimpNegUnit  : 24
% 15.09/7.13  #BackRed      : 72
% 15.09/7.13  
% 15.09/7.13  #Partial instantiations: 0
% 15.09/7.13  #Strategies tried      : 1
% 15.09/7.13  
% 15.09/7.13  Timing (in seconds)
% 15.09/7.13  ----------------------
% 15.09/7.13  Preprocessing        : 0.32
% 15.09/7.13  Parsing              : 0.17
% 15.09/7.13  CNF conversion       : 0.03
% 15.09/7.13  Main loop            : 6.02
% 15.09/7.14  Inferencing          : 1.07
% 15.09/7.14  Reduction            : 1.19
% 15.09/7.14  Demodulation         : 0.72
% 15.09/7.14  BG Simplification    : 0.08
% 15.09/7.14  Subsumption          : 3.41
% 15.09/7.14  Abstraction          : 0.16
% 15.09/7.14  MUC search           : 0.00
% 15.09/7.14  Cooper               : 0.00
% 15.09/7.14  Total                : 6.39
% 15.09/7.14  Index Insertion      : 0.00
% 15.09/7.14  Index Deletion       : 0.00
% 15.09/7.14  Index Matching       : 0.00
% 15.09/7.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
