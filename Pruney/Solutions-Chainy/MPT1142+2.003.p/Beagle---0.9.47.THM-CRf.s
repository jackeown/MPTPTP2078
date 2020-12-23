%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:21 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 146 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  155 ( 644 expanded)
%              Number of equality atoms :   13 (  22 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r1_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(c_12,plain,(
    ~ r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    v5_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    l1_orders_2('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_1')) ),
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

tff(c_44,plain,(
    ! [A_46,C_47,B_48] :
      ( ~ r2_orders_2(A_46,C_47,B_48)
      | ~ r1_orders_2(A_46,B_48,C_47)
      | ~ m1_subset_1(C_47,u1_struct_0(A_46))
      | ~ m1_subset_1(B_48,u1_struct_0(A_46))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_46,plain,
    ( ~ r1_orders_2('#skF_1','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1')
    | ~ v5_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_44])).

tff(c_49,plain,(
    ~ r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_14,c_16,c_46])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
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

tff(c_111,plain,(
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

tff(c_113,plain,(
    ! [B_55] :
      ( r1_orders_2('#skF_1',B_55,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_55,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
      | ~ m1_subset_1(B_55,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1')
      | ~ v4_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_43,c_111])).

tff(c_163,plain,(
    ! [B_60] :
      ( r1_orders_2('#skF_1',B_60,'#skF_4')
      | ~ r1_orders_2('#skF_1',B_60,'#skF_3')
      | ~ m1_subset_1(B_60,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_16,c_14,c_113])).

tff(c_172,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_4')
    | ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_163])).

tff(c_178,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_172])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_178])).

tff(c_181,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_183,plain,(
    r1_orders_2('#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_35])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_183])).

tff(c_189,plain,(
    ~ r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_32,plain,
    ( r2_orders_2('#skF_1','#skF_2','#skF_3')
    | r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_190,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_32])).

tff(c_192,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_orders_2(A_63,B_64,C_65)
      | ~ r2_orders_2(A_63,B_64,C_65)
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_194,plain,
    ( r1_orders_2('#skF_1','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_orders_2('#skF_1') ),
    inference(resolution,[status(thm)],[c_190,c_192])).

tff(c_199,plain,(
    r1_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_16,c_194])).

tff(c_201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_199])).

tff(c_203,plain,(
    ~ r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_26,plain,
    ( r1_orders_2('#skF_1','#skF_3','#skF_4')
    | r2_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_205,plain,(
    r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_26])).

tff(c_220,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_orders_2(A_74,B_75,C_76)
      | C_76 = B_75
      | ~ r1_orders_2(A_74,B_75,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_74))
      | ~ m1_subset_1(B_75,u1_struct_0(A_74))
      | ~ l1_orders_2(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_222,plain,(
    ! [B_75] :
      ( r2_orders_2('#skF_1',B_75,'#skF_4')
      | B_75 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_75,'#skF_4')
      | ~ m1_subset_1(B_75,u1_struct_0('#skF_1'))
      | ~ l1_orders_2('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_14,c_220])).

tff(c_236,plain,(
    ! [B_77] :
      ( r2_orders_2('#skF_1',B_77,'#skF_4')
      | B_77 = '#skF_4'
      | ~ r1_orders_2('#skF_1',B_77,'#skF_4')
      | ~ m1_subset_1(B_77,u1_struct_0('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_222])).

tff(c_242,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_orders_2('#skF_1','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_236])).

tff(c_250,plain,
    ( r2_orders_2('#skF_1','#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_242])).

tff(c_251,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_203,c_250])).

tff(c_202,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_259,plain,(
    r2_orders_2('#skF_1','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_202])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_259])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:38:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  
% 2.18/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.28  %$ r2_orders_2 > r1_orders_2 > m1_subset_1 > v5_orders_2 > v4_orders_2 > l1_orders_2 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.18/1.28  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.18/1.28  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 2.18/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.18/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.28  
% 2.18/1.30  tff(f_100, negated_conjecture, ~(![A]: (((v4_orders_2(A) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((r2_orders_2(A, B, C) & r1_orders_2(A, C, D)) | (r1_orders_2(A, B, C) & r2_orders_2(A, C, D))) => r2_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_orders_2)).
% 2.18/1.30  tff(f_74, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r1_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_orders_2)).
% 2.18/1.30  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 2.18/1.30  tff(f_59, axiom, (![A]: ((v4_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r1_orders_2(A, B, C) & r1_orders_2(A, C, D)) => r1_orders_2(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_orders_2)).
% 2.18/1.30  tff(c_12, plain, (~r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_22, plain, (v5_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_20, plain, (l1_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_14, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_16, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_28, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_33, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_28])).
% 2.18/1.30  tff(c_44, plain, (![A_46, C_47, B_48]: (~r2_orders_2(A_46, C_47, B_48) | ~r1_orders_2(A_46, B_48, C_47) | ~m1_subset_1(C_47, u1_struct_0(A_46)) | ~m1_subset_1(B_48, u1_struct_0(A_46)) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.18/1.30  tff(c_46, plain, (~r1_orders_2('#skF_1', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v5_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_33, c_44])).
% 2.18/1.30  tff(c_49, plain, (~r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_14, c_16, c_46])).
% 2.18/1.30  tff(c_18, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_50, plain, (![A_49, B_50, C_51]: (r2_orders_2(A_49, B_50, C_51) | C_51=B_50 | ~r1_orders_2(A_49, B_50, C_51) | ~m1_subset_1(C_51, u1_struct_0(A_49)) | ~m1_subset_1(B_50, u1_struct_0(A_49)) | ~l1_orders_2(A_49))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.30  tff(c_52, plain, (![B_50]: (r2_orders_2('#skF_1', B_50, '#skF_4') | B_50='#skF_4' | ~r1_orders_2('#skF_1', B_50, '#skF_4') | ~m1_subset_1(B_50, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_50])).
% 2.18/1.30  tff(c_66, plain, (![B_52]: (r2_orders_2('#skF_1', B_52, '#skF_4') | B_52='#skF_4' | ~r1_orders_2('#skF_1', B_52, '#skF_4') | ~m1_subset_1(B_52, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_52])).
% 2.18/1.30  tff(c_75, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4') | '#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_66])).
% 2.18/1.30  tff(c_83, plain, ('#skF_2'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_12, c_75])).
% 2.18/1.30  tff(c_84, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_83])).
% 2.18/1.30  tff(c_30, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_35, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.18/1.30  tff(c_24, plain, (v4_orders_2('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_38, plain, (![A_43, B_44, C_45]: (r1_orders_2(A_43, B_44, C_45) | ~r2_orders_2(A_43, B_44, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~m1_subset_1(B_44, u1_struct_0(A_43)) | ~l1_orders_2(A_43))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.30  tff(c_40, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_33, c_38])).
% 2.18/1.30  tff(c_43, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_14, c_40])).
% 2.18/1.30  tff(c_111, plain, (![A_54, B_55, D_56, C_57]: (r1_orders_2(A_54, B_55, D_56) | ~r1_orders_2(A_54, C_57, D_56) | ~r1_orders_2(A_54, B_55, C_57) | ~m1_subset_1(D_56, u1_struct_0(A_54)) | ~m1_subset_1(C_57, u1_struct_0(A_54)) | ~m1_subset_1(B_55, u1_struct_0(A_54)) | ~l1_orders_2(A_54) | ~v4_orders_2(A_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.18/1.30  tff(c_113, plain, (![B_55]: (r1_orders_2('#skF_1', B_55, '#skF_4') | ~r1_orders_2('#skF_1', B_55, '#skF_3') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1(B_55, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1') | ~v4_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_43, c_111])).
% 2.18/1.30  tff(c_163, plain, (![B_60]: (r1_orders_2('#skF_1', B_60, '#skF_4') | ~r1_orders_2('#skF_1', B_60, '#skF_3') | ~m1_subset_1(B_60, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_16, c_14, c_113])).
% 2.18/1.30  tff(c_172, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4') | ~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_163])).
% 2.18/1.30  tff(c_178, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_172])).
% 2.18/1.30  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_178])).
% 2.18/1.30  tff(c_181, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_83])).
% 2.18/1.30  tff(c_183, plain, (r1_orders_2('#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_35])).
% 2.18/1.30  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_183])).
% 2.18/1.30  tff(c_189, plain, (~r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 2.18/1.30  tff(c_32, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3') | r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_190, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_189, c_32])).
% 2.18/1.30  tff(c_192, plain, (![A_63, B_64, C_65]: (r1_orders_2(A_63, B_64, C_65) | ~r2_orders_2(A_63, B_64, C_65) | ~m1_subset_1(C_65, u1_struct_0(A_63)) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_orders_2(A_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.30  tff(c_194, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1')), inference(resolution, [status(thm)], [c_190, c_192])).
% 2.18/1.30  tff(c_199, plain, (r1_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_16, c_194])).
% 2.18/1.30  tff(c_201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_199])).
% 2.18/1.30  tff(c_203, plain, (~r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.18/1.30  tff(c_26, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4') | r2_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.18/1.30  tff(c_205, plain, (r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_203, c_26])).
% 2.18/1.30  tff(c_220, plain, (![A_74, B_75, C_76]: (r2_orders_2(A_74, B_75, C_76) | C_76=B_75 | ~r1_orders_2(A_74, B_75, C_76) | ~m1_subset_1(C_76, u1_struct_0(A_74)) | ~m1_subset_1(B_75, u1_struct_0(A_74)) | ~l1_orders_2(A_74))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.18/1.30  tff(c_222, plain, (![B_75]: (r2_orders_2('#skF_1', B_75, '#skF_4') | B_75='#skF_4' | ~r1_orders_2('#skF_1', B_75, '#skF_4') | ~m1_subset_1(B_75, u1_struct_0('#skF_1')) | ~l1_orders_2('#skF_1'))), inference(resolution, [status(thm)], [c_14, c_220])).
% 2.18/1.30  tff(c_236, plain, (![B_77]: (r2_orders_2('#skF_1', B_77, '#skF_4') | B_77='#skF_4' | ~r1_orders_2('#skF_1', B_77, '#skF_4') | ~m1_subset_1(B_77, u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_222])).
% 2.18/1.30  tff(c_242, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~r1_orders_2('#skF_1', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_16, c_236])).
% 2.18/1.30  tff(c_250, plain, (r2_orders_2('#skF_1', '#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_242])).
% 2.18/1.30  tff(c_251, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_203, c_250])).
% 2.18/1.30  tff(c_202, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.18/1.30  tff(c_259, plain, (r2_orders_2('#skF_1', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_202])).
% 2.18/1.30  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_259])).
% 2.18/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.30  
% 2.18/1.30  Inference rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Ref     : 0
% 2.18/1.30  #Sup     : 34
% 2.18/1.30  #Fact    : 0
% 2.18/1.30  #Define  : 0
% 2.18/1.30  #Split   : 5
% 2.18/1.30  #Chain   : 0
% 2.18/1.30  #Close   : 0
% 2.18/1.30  
% 2.18/1.30  Ordering : KBO
% 2.18/1.30  
% 2.18/1.30  Simplification rules
% 2.18/1.30  ----------------------
% 2.18/1.30  #Subsume      : 5
% 2.18/1.30  #Demod        : 64
% 2.18/1.30  #Tautology    : 12
% 2.18/1.30  #SimpNegUnit  : 11
% 2.18/1.30  #BackRed      : 13
% 2.18/1.30  
% 2.18/1.30  #Partial instantiations: 0
% 2.18/1.30  #Strategies tried      : 1
% 2.18/1.30  
% 2.18/1.30  Timing (in seconds)
% 2.18/1.30  ----------------------
% 2.18/1.30  Preprocessing        : 0.29
% 2.18/1.31  Parsing              : 0.16
% 2.18/1.31  CNF conversion       : 0.02
% 2.18/1.31  Main loop            : 0.24
% 2.18/1.31  Inferencing          : 0.09
% 2.18/1.31  Reduction            : 0.07
% 2.18/1.31  Demodulation         : 0.05
% 2.18/1.31  BG Simplification    : 0.01
% 2.18/1.31  Subsumption          : 0.04
% 2.18/1.31  Abstraction          : 0.01
% 2.18/1.31  MUC search           : 0.00
% 2.18/1.31  Cooper               : 0.00
% 2.18/1.31  Total                : 0.56
% 2.18/1.31  Index Insertion      : 0.00
% 2.18/1.31  Index Deletion       : 0.00
% 2.18/1.31  Index Matching       : 0.00
% 2.18/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
