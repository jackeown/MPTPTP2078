%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:45 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 153 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  206 ( 937 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_121,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_70,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_14,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [B_62,C_63,A_64] :
      ( m1_pre_topc(B_62,C_63)
      | ~ r1_tarski(u1_struct_0(B_62),u1_struct_0(C_63))
      | ~ m1_pre_topc(C_63,A_64)
      | ~ m1_pre_topc(B_62,A_64)
      | ~ l1_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_131,plain,(
    ! [B_65,A_66] :
      ( m1_pre_topc(B_65,B_65)
      | ~ m1_pre_topc(B_65,A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_135,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_131])).

tff(c_143,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_135])).

tff(c_40,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_43,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_173,plain,(
    ! [D_70,C_67,E_69,B_71,A_68] :
      ( m1_pre_topc(k2_tsep_1(A_68,B_71,C_67),k2_tsep_1(A_68,D_70,E_69))
      | r1_tsep_1(B_71,C_67)
      | ~ m1_pre_topc(C_67,E_69)
      | ~ m1_pre_topc(B_71,D_70)
      | ~ m1_pre_topc(E_69,A_68)
      | v2_struct_0(E_69)
      | ~ m1_pre_topc(D_70,A_68)
      | v2_struct_0(D_70)
      | ~ m1_pre_topc(C_67,A_68)
      | v2_struct_0(C_67)
      | ~ m1_pre_topc(B_71,A_68)
      | v2_struct_0(B_71)
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_36,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_51,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_180,plain,
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
    inference(resolution,[status(thm)],[c_173,c_51])).

tff(c_185,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_20,c_16,c_143,c_43,c_180])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_26,c_22,c_18,c_14,c_185])).

tff(c_188,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_231,plain,(
    ! [B_78,C_79,A_80] :
      ( m1_pre_topc(B_78,C_79)
      | ~ r1_tarski(u1_struct_0(B_78),u1_struct_0(C_79))
      | ~ m1_pre_topc(C_79,A_80)
      | ~ m1_pre_topc(B_78,A_80)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_245,plain,(
    ! [B_81,A_82] :
      ( m1_pre_topc(B_81,B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_231])).

tff(c_255,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_245])).

tff(c_266,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_255])).

tff(c_293,plain,(
    ! [B_87,D_86,E_85,C_83,A_84] :
      ( m1_pre_topc(k2_tsep_1(A_84,B_87,C_83),k2_tsep_1(A_84,D_86,E_85))
      | r1_tsep_1(B_87,C_83)
      | ~ m1_pre_topc(C_83,E_85)
      | ~ m1_pre_topc(B_87,D_86)
      | ~ m1_pre_topc(E_85,A_84)
      | v2_struct_0(E_85)
      | ~ m1_pre_topc(D_86,A_84)
      | v2_struct_0(D_86)
      | ~ m1_pre_topc(C_83,A_84)
      | v2_struct_0(C_83)
      | ~ m1_pre_topc(B_87,A_84)
      | v2_struct_0(B_87)
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_189,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3'))
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_192,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_34])).

tff(c_300,plain,
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
    inference(resolution,[status(thm)],[c_293,c_192])).

tff(c_305,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_20,c_16,c_188,c_266,c_300])).

tff(c_307,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_26,c_22,c_18,c_14,c_305])).

tff(c_308,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_350,plain,(
    ! [B_96,C_97,A_98] :
      ( m1_pre_topc(B_96,C_97)
      | ~ r1_tarski(u1_struct_0(B_96),u1_struct_0(C_97))
      | ~ m1_pre_topc(C_97,A_98)
      | ~ m1_pre_topc(B_96,A_98)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_364,plain,(
    ! [B_99,A_100] :
      ( m1_pre_topc(B_99,B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(resolution,[status(thm)],[c_6,c_350])).

tff(c_370,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_364])).

tff(c_379,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_370])).

tff(c_407,plain,(
    ! [A_102,D_104,C_101,B_105,E_103] :
      ( m1_pre_topc(k2_tsep_1(A_102,B_105,C_101),k2_tsep_1(A_102,D_104,E_103))
      | r1_tsep_1(B_105,C_101)
      | ~ m1_pre_topc(C_101,E_103)
      | ~ m1_pre_topc(B_105,D_104)
      | ~ m1_pre_topc(E_103,A_102)
      | v2_struct_0(E_103)
      | ~ m1_pre_topc(D_104,A_102)
      | v2_struct_0(D_104)
      | ~ m1_pre_topc(C_101,A_102)
      | v2_struct_0(C_101)
      | ~ m1_pre_topc(B_105,A_102)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_309,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3'))
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_318,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_309,c_38])).

tff(c_414,plain,
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
    inference(resolution,[status(thm)],[c_407,c_318])).

tff(c_419,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_20,c_16,c_308,c_379,c_414])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_26,c_22,c_18,c_14,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.50  
% 2.60/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.50  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_tsep_1 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.60/1.50  
% 2.60/1.50  %Foreground sorts:
% 2.60/1.50  
% 2.60/1.50  
% 2.60/1.50  %Background operators:
% 2.60/1.50  
% 2.60/1.50  
% 2.60/1.50  %Foreground operators:
% 2.60/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.60/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.60/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.60/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.60/1.50  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 2.60/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.60/1.50  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.60/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.60/1.50  
% 2.60/1.52  tff(f_121, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((m1_pre_topc(B, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, C))) & (m1_pre_topc(C, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, B, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tmap_1)).
% 2.60/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.60/1.52  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.60/1.52  tff(f_70, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, E)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tmap_1)).
% 2.60/1.52  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_22, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_18, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_14, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_16, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.60/1.52  tff(c_116, plain, (![B_62, C_63, A_64]: (m1_pre_topc(B_62, C_63) | ~r1_tarski(u1_struct_0(B_62), u1_struct_0(C_63)) | ~m1_pre_topc(C_63, A_64) | ~m1_pre_topc(B_62, A_64) | ~l1_pre_topc(A_64) | ~v2_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.52  tff(c_131, plain, (![B_65, A_66]: (m1_pre_topc(B_65, B_65) | ~m1_pre_topc(B_65, A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66))), inference(resolution, [status(thm)], [c_6, c_116])).
% 2.60/1.52  tff(c_135, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_131])).
% 2.60/1.52  tff(c_143, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_135])).
% 2.60/1.52  tff(c_40, plain, (m1_pre_topc('#skF_2', '#skF_4') | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_43, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_40])).
% 2.60/1.52  tff(c_173, plain, (![D_70, C_67, E_69, B_71, A_68]: (m1_pre_topc(k2_tsep_1(A_68, B_71, C_67), k2_tsep_1(A_68, D_70, E_69)) | r1_tsep_1(B_71, C_67) | ~m1_pre_topc(C_67, E_69) | ~m1_pre_topc(B_71, D_70) | ~m1_pre_topc(E_69, A_68) | v2_struct_0(E_69) | ~m1_pre_topc(D_70, A_68) | v2_struct_0(D_70) | ~m1_pre_topc(C_67, A_68) | v2_struct_0(C_67) | ~m1_pre_topc(B_71, A_68) | v2_struct_0(B_71) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.52  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_51, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_36])).
% 2.60/1.52  tff(c_180, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_173, c_51])).
% 2.60/1.52  tff(c_185, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_20, c_16, c_143, c_43, c_180])).
% 2.60/1.52  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_26, c_22, c_18, c_14, c_185])).
% 2.60/1.52  tff(c_188, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_36])).
% 2.60/1.52  tff(c_231, plain, (![B_78, C_79, A_80]: (m1_pre_topc(B_78, C_79) | ~r1_tarski(u1_struct_0(B_78), u1_struct_0(C_79)) | ~m1_pre_topc(C_79, A_80) | ~m1_pre_topc(B_78, A_80) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.52  tff(c_245, plain, (![B_81, A_82]: (m1_pre_topc(B_81, B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82))), inference(resolution, [status(thm)], [c_6, c_231])).
% 2.60/1.52  tff(c_255, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_245])).
% 2.60/1.52  tff(c_266, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_255])).
% 2.60/1.52  tff(c_293, plain, (![B_87, D_86, E_85, C_83, A_84]: (m1_pre_topc(k2_tsep_1(A_84, B_87, C_83), k2_tsep_1(A_84, D_86, E_85)) | r1_tsep_1(B_87, C_83) | ~m1_pre_topc(C_83, E_85) | ~m1_pre_topc(B_87, D_86) | ~m1_pre_topc(E_85, A_84) | v2_struct_0(E_85) | ~m1_pre_topc(D_86, A_84) | v2_struct_0(D_86) | ~m1_pre_topc(C_83, A_84) | v2_struct_0(C_83) | ~m1_pre_topc(B_87, A_84) | v2_struct_0(B_87) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.52  tff(c_189, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_36])).
% 2.60/1.52  tff(c_34, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_192, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_34])).
% 2.60/1.52  tff(c_300, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_293, c_192])).
% 2.60/1.52  tff(c_305, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_20, c_16, c_188, c_266, c_300])).
% 2.60/1.52  tff(c_307, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_26, c_22, c_18, c_14, c_305])).
% 2.60/1.52  tff(c_308, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.60/1.52  tff(c_350, plain, (![B_96, C_97, A_98]: (m1_pre_topc(B_96, C_97) | ~r1_tarski(u1_struct_0(B_96), u1_struct_0(C_97)) | ~m1_pre_topc(C_97, A_98) | ~m1_pre_topc(B_96, A_98) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.60/1.52  tff(c_364, plain, (![B_99, A_100]: (m1_pre_topc(B_99, B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(resolution, [status(thm)], [c_6, c_350])).
% 2.60/1.52  tff(c_370, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_364])).
% 2.60/1.52  tff(c_379, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_370])).
% 2.60/1.52  tff(c_407, plain, (![A_102, D_104, C_101, B_105, E_103]: (m1_pre_topc(k2_tsep_1(A_102, B_105, C_101), k2_tsep_1(A_102, D_104, E_103)) | r1_tsep_1(B_105, C_101) | ~m1_pre_topc(C_101, E_103) | ~m1_pre_topc(B_105, D_104) | ~m1_pre_topc(E_103, A_102) | v2_struct_0(E_103) | ~m1_pre_topc(D_104, A_102) | v2_struct_0(D_104) | ~m1_pre_topc(C_101, A_102) | v2_struct_0(C_101) | ~m1_pre_topc(B_105, A_102) | v2_struct_0(B_105) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.60/1.52  tff(c_309, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_40])).
% 2.60/1.52  tff(c_38, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.60/1.52  tff(c_318, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_309, c_38])).
% 2.60/1.52  tff(c_414, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_407, c_318])).
% 2.60/1.52  tff(c_419, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_20, c_16, c_308, c_379, c_414])).
% 2.60/1.52  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_26, c_22, c_18, c_14, c_419])).
% 2.60/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.52  
% 2.60/1.52  Inference rules
% 2.60/1.52  ----------------------
% 2.60/1.52  #Ref     : 0
% 2.60/1.52  #Sup     : 82
% 2.60/1.52  #Fact    : 0
% 2.60/1.52  #Define  : 0
% 2.60/1.52  #Split   : 11
% 2.60/1.52  #Chain   : 0
% 2.60/1.52  #Close   : 0
% 2.60/1.52  
% 2.60/1.52  Ordering : KBO
% 2.60/1.52  
% 2.60/1.52  Simplification rules
% 2.60/1.52  ----------------------
% 2.60/1.52  #Subsume      : 9
% 2.60/1.52  #Demod        : 81
% 2.60/1.52  #Tautology    : 25
% 2.60/1.52  #SimpNegUnit  : 4
% 2.60/1.52  #BackRed      : 0
% 2.60/1.52  
% 2.60/1.52  #Partial instantiations: 0
% 2.60/1.52  #Strategies tried      : 1
% 2.60/1.52  
% 2.60/1.52  Timing (in seconds)
% 2.60/1.52  ----------------------
% 2.60/1.52  Preprocessing        : 0.36
% 2.60/1.52  Parsing              : 0.22
% 2.60/1.52  CNF conversion       : 0.03
% 2.60/1.52  Main loop            : 0.29
% 2.60/1.52  Inferencing          : 0.10
% 2.60/1.52  Reduction            : 0.08
% 2.60/1.52  Demodulation         : 0.06
% 2.60/1.52  BG Simplification    : 0.02
% 2.60/1.52  Subsumption          : 0.06
% 2.60/1.52  Abstraction          : 0.01
% 2.60/1.52  MUC search           : 0.00
% 2.60/1.52  Cooper               : 0.00
% 2.60/1.52  Total                : 0.68
% 2.60/1.52  Index Insertion      : 0.00
% 2.60/1.52  Index Deletion       : 0.00
% 2.60/1.52  Index Matching       : 0.00
% 2.60/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
