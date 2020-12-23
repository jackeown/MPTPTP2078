%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:45 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 148 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  185 ( 868 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ~ r1_tsep_1(B,C)
                     => ( ( m1_pre_topc(B,D)
                         => m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,C)) )
                        & ( m1_pre_topc(C,D)
                         => m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,B,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ! [E] :
                      ( ( ~ v2_struct_0(E)
                        & m1_pre_topc(E,A) )
                     => ( ( m1_pre_topc(B,D)
                          & m1_pre_topc(C,E) )
                       => ( r1_tsep_1(B,C)
                          | m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,E)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_123,plain,(
    ! [B_60,A_61] :
      ( l1_pre_topc(B_60)
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_143,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_132])).

tff(c_6,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_12,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_8,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_18,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_37,plain,(
    ! [B_48,A_49] :
      ( l1_pre_topc(B_48)
      | ~ m1_pre_topc(B_48,A_49)
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_37])).

tff(c_57,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_52,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_37])).

tff(c_63,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_52])).

tff(c_34,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_68,plain,(
    ! [B_51,E_52,D_50,C_53,A_54] :
      ( m1_pre_topc(k2_tsep_1(A_54,B_51,C_53),k2_tsep_1(A_54,D_50,E_52))
      | r1_tsep_1(B_51,C_53)
      | ~ m1_pre_topc(C_53,E_52)
      | ~ m1_pre_topc(B_51,D_50)
      | ~ m1_pre_topc(E_52,A_54)
      | v2_struct_0(E_52)
      | ~ m1_pre_topc(D_50,A_54)
      | v2_struct_0(D_50)
      | ~ m1_pre_topc(C_53,A_54)
      | v2_struct_0(C_53)
      | ~ m1_pre_topc(B_51,A_54)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_67,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_71,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_67])).

tff(c_77,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_14,c_10,c_36,c_71])).

tff(c_78,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_16,c_12,c_8,c_77])).

tff(c_82,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_78])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_82])).

tff(c_87,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_102,plain,(
    ! [D_55,B_56,A_59,E_57,C_58] :
      ( m1_pre_topc(k2_tsep_1(A_59,B_56,C_58),k2_tsep_1(A_59,D_55,E_57))
      | r1_tsep_1(B_56,C_58)
      | ~ m1_pre_topc(C_58,E_57)
      | ~ m1_pre_topc(B_56,D_55)
      | ~ m1_pre_topc(E_57,A_59)
      | v2_struct_0(E_57)
      | ~ m1_pre_topc(D_55,A_59)
      | v2_struct_0(D_55)
      | ~ m1_pre_topc(C_58,A_59)
      | v2_struct_0(C_58)
      | ~ m1_pre_topc(B_56,A_59)
      | v2_struct_0(B_56)
      | ~ l1_pre_topc(A_59)
      | ~ v2_pre_topc(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_88,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_101,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_28])).

tff(c_105,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_101])).

tff(c_111,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_14,c_10,c_87,c_105])).

tff(c_112,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_16,c_12,c_8,c_111])).

tff(c_116,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_116])).

tff(c_121,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_154,plain,(
    ! [B_63,A_66,D_62,C_65,E_64] :
      ( m1_pre_topc(k2_tsep_1(A_66,B_63,C_65),k2_tsep_1(A_66,D_62,E_64))
      | r1_tsep_1(B_63,C_65)
      | ~ m1_pre_topc(C_65,E_64)
      | ~ m1_pre_topc(B_63,D_62)
      | ~ m1_pre_topc(E_64,A_66)
      | v2_struct_0(E_64)
      | ~ m1_pre_topc(D_62,A_66)
      | v2_struct_0(D_62)
      | ~ m1_pre_topc(C_65,A_66)
      | v2_struct_0(C_65)
      | ~ m1_pre_topc(B_63,A_66)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_122,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3'))
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_150,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_32])).

tff(c_157,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_154,c_150])).

tff(c_163,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_18,c_14,c_10,c_121,c_157])).

tff(c_164,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_20,c_16,c_12,c_8,c_163])).

tff(c_168,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_164])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_168])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.19  
% 2.07/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.19  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.19  
% 2.07/1.19  %Foreground sorts:
% 2.07/1.19  
% 2.07/1.19  
% 2.07/1.19  %Background operators:
% 2.07/1.19  
% 2.07/1.19  
% 2.07/1.19  %Foreground operators:
% 2.07/1.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.07/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.07/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.07/1.19  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.07/1.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.07/1.19  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.07/1.19  
% 2.07/1.21  tff(f_112, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((m1_pre_topc(B, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, C))) & (m1_pre_topc(C, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, B, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tmap_1)).
% 2.07/1.21  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.07/1.21  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 2.07/1.21  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_tmap_1)).
% 2.07/1.21  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_14, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_123, plain, (![B_60, A_61]: (l1_pre_topc(B_60) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.21  tff(c_132, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.07/1.21  tff(c_143, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_132])).
% 2.07/1.21  tff(c_6, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.07/1.21  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_20, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_16, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_12, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_8, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_18, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_10, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_37, plain, (![B_48, A_49]: (l1_pre_topc(B_48) | ~m1_pre_topc(B_48, A_49) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.21  tff(c_46, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_37])).
% 2.07/1.21  tff(c_57, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_46])).
% 2.07/1.21  tff(c_52, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_18, c_37])).
% 2.07/1.21  tff(c_63, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_52])).
% 2.07/1.21  tff(c_34, plain, (m1_pre_topc('#skF_2', '#skF_4') | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_36, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.07/1.21  tff(c_68, plain, (![B_51, E_52, D_50, C_53, A_54]: (m1_pre_topc(k2_tsep_1(A_54, B_51, C_53), k2_tsep_1(A_54, D_50, E_52)) | r1_tsep_1(B_51, C_53) | ~m1_pre_topc(C_53, E_52) | ~m1_pre_topc(B_51, D_50) | ~m1_pre_topc(E_52, A_54) | v2_struct_0(E_52) | ~m1_pre_topc(D_50, A_54) | v2_struct_0(D_50) | ~m1_pre_topc(C_53, A_54) | v2_struct_0(C_53) | ~m1_pre_topc(B_51, A_54) | v2_struct_0(B_51) | ~l1_pre_topc(A_54) | ~v2_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.21  tff(c_30, plain, (m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_67, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_30])).
% 2.07/1.21  tff(c_71, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_68, c_67])).
% 2.07/1.21  tff(c_77, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_14, c_10, c_36, c_71])).
% 2.07/1.21  tff(c_78, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_16, c_12, c_8, c_77])).
% 2.07/1.21  tff(c_82, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_6, c_78])).
% 2.07/1.21  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_82])).
% 2.07/1.21  tff(c_87, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.07/1.21  tff(c_102, plain, (![D_55, B_56, A_59, E_57, C_58]: (m1_pre_topc(k2_tsep_1(A_59, B_56, C_58), k2_tsep_1(A_59, D_55, E_57)) | r1_tsep_1(B_56, C_58) | ~m1_pre_topc(C_58, E_57) | ~m1_pre_topc(B_56, D_55) | ~m1_pre_topc(E_57, A_59) | v2_struct_0(E_57) | ~m1_pre_topc(D_55, A_59) | v2_struct_0(D_55) | ~m1_pre_topc(C_58, A_59) | v2_struct_0(C_58) | ~m1_pre_topc(B_56, A_59) | v2_struct_0(B_56) | ~l1_pre_topc(A_59) | ~v2_pre_topc(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.21  tff(c_88, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_30])).
% 2.07/1.21  tff(c_28, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_101, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_28])).
% 2.07/1.21  tff(c_105, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_102, c_101])).
% 2.07/1.21  tff(c_111, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_14, c_10, c_87, c_105])).
% 2.07/1.21  tff(c_112, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_16, c_12, c_8, c_111])).
% 2.07/1.21  tff(c_116, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_112])).
% 2.07/1.21  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_116])).
% 2.07/1.21  tff(c_121, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.07/1.21  tff(c_154, plain, (![B_63, A_66, D_62, C_65, E_64]: (m1_pre_topc(k2_tsep_1(A_66, B_63, C_65), k2_tsep_1(A_66, D_62, E_64)) | r1_tsep_1(B_63, C_65) | ~m1_pre_topc(C_65, E_64) | ~m1_pre_topc(B_63, D_62) | ~m1_pre_topc(E_64, A_66) | v2_struct_0(E_64) | ~m1_pre_topc(D_62, A_66) | v2_struct_0(D_62) | ~m1_pre_topc(C_65, A_66) | v2_struct_0(C_65) | ~m1_pre_topc(B_63, A_66) | v2_struct_0(B_63) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.07/1.21  tff(c_122, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.07/1.21  tff(c_32, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.07/1.21  tff(c_150, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_122, c_32])).
% 2.07/1.21  tff(c_157, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_154, c_150])).
% 2.07/1.21  tff(c_163, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_18, c_14, c_10, c_121, c_157])).
% 2.07/1.21  tff(c_164, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_20, c_16, c_12, c_8, c_163])).
% 2.07/1.21  tff(c_168, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_6, c_164])).
% 2.07/1.21  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_143, c_168])).
% 2.07/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  Inference rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Ref     : 0
% 2.07/1.21  #Sup     : 21
% 2.07/1.21  #Fact    : 0
% 2.07/1.21  #Define  : 0
% 2.07/1.21  #Split   : 3
% 2.07/1.21  #Chain   : 0
% 2.07/1.21  #Close   : 0
% 2.07/1.21  
% 2.07/1.21  Ordering : KBO
% 2.07/1.21  
% 2.07/1.21  Simplification rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Subsume      : 2
% 2.07/1.21  #Demod        : 36
% 2.07/1.21  #Tautology    : 7
% 2.07/1.21  #SimpNegUnit  : 4
% 2.07/1.21  #BackRed      : 0
% 2.07/1.21  
% 2.07/1.21  #Partial instantiations: 0
% 2.07/1.21  #Strategies tried      : 1
% 2.07/1.21  
% 2.07/1.21  Timing (in seconds)
% 2.07/1.21  ----------------------
% 2.07/1.21  Preprocessing        : 0.28
% 2.07/1.21  Parsing              : 0.15
% 2.07/1.21  CNF conversion       : 0.03
% 2.07/1.21  Main loop            : 0.18
% 2.07/1.21  Inferencing          : 0.07
% 2.07/1.21  Reduction            : 0.05
% 2.07/1.21  Demodulation         : 0.04
% 2.07/1.21  BG Simplification    : 0.01
% 2.07/1.21  Subsumption          : 0.03
% 2.07/1.21  Abstraction          : 0.01
% 2.07/1.21  MUC search           : 0.00
% 2.07/1.21  Cooper               : 0.00
% 2.07/1.21  Total                : 0.49
% 2.07/1.21  Index Insertion      : 0.00
% 2.07/1.21  Index Deletion       : 0.00
% 2.07/1.21  Index Matching       : 0.00
% 2.07/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
