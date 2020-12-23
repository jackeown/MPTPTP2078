%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 181 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  172 ( 810 expanded)
%              Number of equality atoms :   18 (  36 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( ( r2_orders_2(A,B,C)
                          & r1_orders_2(A,C,D) )
                        | ( r1_orders_2(A,B,C)
                          & r2_orders_2(A,C,D) ) )
                     => r2_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v4_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( r1_orders_2(A,B,C)
                      & r1_orders_2(A,C,D) )
                   => r1_orders_2(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_12,plain,(
    ~ r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    ! [A_49,B_50,C_51] :
      ( r2_orders_2(A_49,B_50,C_51)
      | C_51 = B_50
      | ~ r1_orders_2(A_49,B_50,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(A_49))
      | ~ m1_subset_1(B_50,u1_struct_0(A_49))
      | ~ l1_orders_2(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [B_50] :
      ( r2_orders_2('#skF_1',B_50,'#skF_4')
      | B_50 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_50,'#skF_4')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_50])).

tff(c_66,plain,(
    ! [B_52] :
      ( r2_orders_2('#skF_1',B_52,'#skF_4')
      | B_52 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_52,'#skF_4')
      | ~ m1_subset_1(B_52,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_52])).

tff(c_75,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_4')
    | '#skF_2' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_66])).

tff(c_83,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_75])).

tff(c_84,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_30,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_35,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_24,plain,(
    v4_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_33,plain,(
    r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_38,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_orders_2(A_43,B_44,C_45)
      | ~ r2_orders_2(A_43,B_44,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ m1_subset_1(B_44,u1_struct_0(A_43))
      | ~ l1_orders_2(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_38])).

tff(c_43,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_14,c_40])).

tff(c_104,plain,(
    ! [A_54,B_55,D_56,C_57] :
      ( r1_orders_2(A_54,B_55,D_56)
      | ~ r1_orders_2(A_54,C_57,D_56)
      | ~ r1_orders_2(A_54,B_55,C_57)
      | ~ m1_subset_1(D_56,u1_struct_0(A_54))
      | ~ m1_subset_1(C_57,u1_struct_0(A_54))
      | ~ m1_subset_1(B_55,u1_struct_0(A_54))
      | ~ l1_orders_2(A_54)
      | ~ v4_orders_2(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_106,plain,(
    ! [B_55] :
      ( r1_orders_2('#skF_1',B_55,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_55,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_43,c_104])).

tff(c_168,plain,(
    ! [B_60] :
      ( r1_orders_2('#skF_1',B_60,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_60,'#skF_3')
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_16,c_14,c_106])).

tff(c_177,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_168])).

tff(c_183,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_177])).

tff(c_185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_183])).

tff(c_186,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_189,plain,(
    ~ r2_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_12])).

tff(c_22,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r2_orders_2(A_46,C_47,B_48)
      | ~ r2_orders_2(A_46,B_48,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_46))
      | ~ m1_subset_1(B_48,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,
    ( ~ r2_orders_2('#skF_1','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_44])).

tff(c_49,plain,(
    ~ r2_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_14,c_16,c_46])).

tff(c_188,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_35])).

tff(c_54,plain,(
    ! [B_50] :
      ( r2_orders_2('#skF_1',B_50,'#skF_3')
      | B_50 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_50,'#skF_3')
      | ~ m1_subset_1(B_50,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_16,c_50])).

tff(c_197,plain,(
    ! [B_61] :
      ( r2_orders_2('#skF_1',B_61,'#skF_3')
      | B_61 = '#skF_3'
      | ~ r1_orders_2('#skF_1',B_61,'#skF_3')
      | ~ m1_subset_1(B_61,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_54])).

tff(c_200,plain,
    ( r2_orders_2('#skF_1','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_197])).

tff(c_206,plain,
    ( r2_orders_2('#skF_1','#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_200])).

tff(c_207,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_206])).

tff(c_214,plain,(
    r2_orders_2('#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_33])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_214])).

tff(c_221,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_222,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_32])).

tff(c_224,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_orders_2(A_64,B_65,C_66)
      | ~ r2_orders_2(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,u1_struct_0(A_64))
      | ~ m1_subset_1(B_65,u1_struct_0(A_64))
      | ~ l1_orders_2(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_226,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_222,c_224])).

tff(c_231,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_226])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_231])).

tff(c_235,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_238,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_26])).

tff(c_246,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_orders_2(A_72,B_73,C_74)
      | C_74 = B_73
      | ~ r1_orders_2(A_72,B_73,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_248,plain,(
    ! [B_73] :
      ( r2_orders_2('#skF_1',B_73,'#skF_4')
      | B_73 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_73,'#skF_4')
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_246])).

tff(c_262,plain,(
    ! [B_75] :
      ( r2_orders_2('#skF_1',B_75,'#skF_4')
      | B_75 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_75,'#skF_4')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_248])).

tff(c_268,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_262])).

tff(c_276,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_268])).

tff(c_277,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_235,c_276])).

tff(c_234,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_284,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_234])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:14:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.24  
% 2.20/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.25  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.20/1.25  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.20/1.25  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.20/1.25  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.20/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.25  
% 2.20/1.26  tff(f_100, negated_conjecture, ~(![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_orders_2)).
% 2.20/1.26  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 2.20/1.26  tff(f_59, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_orders_2)).
% 2.20/1.26  tff(f_74, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 2.20/1.26  tff(c_12, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_20, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_14, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_50, plain, (![A_49, B_50, C_51]: (r2_orders_2(A_49, B_50, C_51) | C_51=B_50 | ~r1_orders_2(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.26  tff(c_52, plain, (![B_50]: (r2_orders_2('#skF_1', B_50, '#skF_4') | B_50='#skF_4' | ~r1_orders_2('#skF_1', B_50, '#skF_4') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_50])).
% 2.20/1.26  tff(c_66, plain, (![B_52]: (r2_orders_2('#skF_1', B_52, '#skF_4') | B_52='#skF_4' | ~r1_orders_2('#skF_1', B_52, '#skF_4') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_52])).
% 2.20/1.26  tff(c_75, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4') | '#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_66])).
% 2.20/1.26  tff(c_83, plain, ('#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12, c_75])).
% 2.20/1.26  tff(c_84, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_83])).
% 2.20/1.26  tff(c_30, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_35, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.20/1.26  tff(c_24, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_16, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_28, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_33, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.20/1.26  tff(c_38, plain, (![A_43, B_44, C_45]: (r1_orders_2(A_43, B_44, C_45) | ~r2_orders_2(A_43, B_44, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.26  tff(c_40, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_33, c_38])).
% 2.20/1.26  tff(c_43, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_14, c_40])).
% 2.20/1.26  tff(c_104, plain, (![A_54, B_55, D_56, C_57]: (r1_orders_2(A_54, B_55, D_56) | ~r1_orders_2(A_54, C_57, D_56) | ~r1_orders_2(A_54, B_55, C_57) | ~m1_subset_1(D_56, u1_struct_0(A_54)) | ~m1_subset_1(C_57, u1_struct_0(A_54)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v4_orders_2(A_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.20/1.26  tff(c_106, plain, (![B_55]: (r1_orders_2('#skF_1', B_55, '#skF_4') | ~r1_orders_2('#skF_1', B_55, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_55, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v4_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_43, c_104])).
% 2.20/1.26  tff(c_168, plain, (![B_60]: (r1_orders_2('#skF_1', B_60, '#skF_4') | ~r1_orders_2('#skF_1', B_60, '#skF_3') | ~m1_subset_1(B_60, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_16, c_14, c_106])).
% 2.20/1.26  tff(c_177, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_168])).
% 2.20/1.26  tff(c_183, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_177])).
% 2.20/1.26  tff(c_185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_183])).
% 2.20/1.26  tff(c_186, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_83])).
% 2.20/1.26  tff(c_189, plain, (~r2_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_12])).
% 2.20/1.26  tff(c_22, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_44, plain, (![A_46, C_47, B_48]: (~r2_orders_2(A_46, C_47, B_48) | ~r2_orders_2(A_46, B_48, C_47) | ~m1_subset_1(C_47, u1_struct_0(A_46)) | ~m1_subset_1(B_48, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.20/1.26  tff(c_46, plain, (~r2_orders_2('#skF_1', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_33, c_44])).
% 2.20/1.26  tff(c_49, plain, (~r2_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_14, c_16, c_46])).
% 2.20/1.26  tff(c_188, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_35])).
% 2.20/1.26  tff(c_54, plain, (![B_50]: (r2_orders_2('#skF_1', B_50, '#skF_3') | B_50='#skF_3' | ~r1_orders_2('#skF_1', B_50, '#skF_3') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_50])).
% 2.20/1.26  tff(c_197, plain, (![B_61]: (r2_orders_2('#skF_1', B_61, '#skF_3') | B_61='#skF_3' | ~r1_orders_2('#skF_1', B_61, '#skF_3') | ~m1_subset_1(B_61, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_54])).
% 2.20/1.26  tff(c_200, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_14, c_197])).
% 2.20/1.26  tff(c_206, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_200])).
% 2.20/1.26  tff(c_207, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_49, c_206])).
% 2.20/1.26  tff(c_214, plain, (r2_orders_2('#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_33])).
% 2.20/1.26  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_214])).
% 2.20/1.26  tff(c_221, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.20/1.26  tff(c_32, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_222, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_221, c_32])).
% 2.20/1.26  tff(c_224, plain, (![A_64, B_65, C_66]: (r1_orders_2(A_64, B_65, C_66) | ~r2_orders_2(A_64, B_65, C_66) | ~m1_subset_1(C_66, u1_struct_0(A_64)) | ~m1_subset_1(B_65, u1_struct_0(A_64)) | ~l1_orders_2(A_64))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.26  tff(c_226, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_222, c_224])).
% 2.20/1.26  tff(c_231, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_226])).
% 2.20/1.26  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_221, c_231])).
% 2.20/1.26  tff(c_235, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.20/1.26  tff(c_26, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.20/1.26  tff(c_238, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_235, c_26])).
% 2.20/1.26  tff(c_246, plain, (![A_72, B_73, C_74]: (r2_orders_2(A_72, B_73, C_74) | C_74=B_73 | ~r1_orders_2(A_72, B_73, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, u1_struct_0(A_72)) | ~l1_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.20/1.26  tff(c_248, plain, (![B_73]: (r2_orders_2('#skF_1', B_73, '#skF_4') | B_73='#skF_4' | ~r1_orders_2('#skF_1', B_73, '#skF_4') | ~m1_subset_1(B_73, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_246])).
% 2.20/1.26  tff(c_262, plain, (![B_75]: (r2_orders_2('#skF_1', B_75, '#skF_4') | B_75='#skF_4' | ~r1_orders_2('#skF_1', B_75, '#skF_4') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_248])).
% 2.20/1.26  tff(c_268, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_262])).
% 2.20/1.26  tff(c_276, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_238, c_268])).
% 2.20/1.26  tff(c_277, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_235, c_276])).
% 2.20/1.26  tff(c_234, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.20/1.26  tff(c_284, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_277, c_234])).
% 2.20/1.26  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_284])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 37
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 7
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 5
% 2.20/1.26  #Demod        : 72
% 2.20/1.26  #Tautology    : 18
% 2.20/1.26  #SimpNegUnit  : 14
% 2.20/1.26  #BackRed      : 18
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.27  Preprocessing        : 0.29
% 2.20/1.27  Parsing              : 0.16
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.20
% 2.20/1.27  Inferencing          : 0.08
% 2.20/1.27  Reduction            : 0.06
% 2.20/1.27  Demodulation         : 0.05
% 2.20/1.27  BG Simplification    : 0.02
% 2.20/1.27  Subsumption          : 0.03
% 2.20/1.27  Abstraction          : 0.01
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.53
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
