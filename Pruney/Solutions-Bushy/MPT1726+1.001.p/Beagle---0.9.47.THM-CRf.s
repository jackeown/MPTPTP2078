%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1726+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:18 EST 2020

% Result     : Theorem 16.84s
% Output     : CNFRefutation 17.12s
% Verified   : 
% Statistics : Number of formulae       :  197 (1108 expanded)
%              Number of leaves         :   29 ( 421 expanded)
%              Depth                    :   26
%              Number of atoms          :  757 (8019 expanded)
%              Number of equality atoms :   13 (  98 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > #nlpp > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_259,negated_conjecture,(
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
                   => ! [E] :
                        ( ( ~ v2_struct_0(E)
                          & m1_pre_topc(E,A) )
                       => ( ( m1_pre_topc(B,C)
                            & m1_pre_topc(D,E) )
                         => ( ( ~ r1_tsep_1(C,E)
                              & ~ r1_tsep_1(k2_tsep_1(A,C,E),k1_tsep_1(A,B,D)) )
                            | ( r1_tsep_1(C,D)
                              & r1_tsep_1(E,B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tmap_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => k1_tsep_1(A,B,C) = k1_tsep_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

tff(f_132,axiom,(
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
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_169,axiom,(
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
                 => ( m1_pre_topc(B,C)
                   => ( ( r1_tsep_1(B,D)
                        & r1_tsep_1(D,B) )
                      | ( ~ r1_tsep_1(C,D)
                        & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

tff(f_213,axiom,(
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
                 => ( ~ r1_tsep_1(B,C)
                   => ( ( m1_pre_topc(B,D)
                       => ( ~ r1_tsep_1(k2_tsep_1(A,D,C),B)
                          & ~ r1_tsep_1(k2_tsep_1(A,C,D),B) ) )
                      & ( m1_pre_topc(C,D)
                       => ( ~ r1_tsep_1(k2_tsep_1(A,B,D),C)
                          & ~ r1_tsep_1(k2_tsep_1(A,D,B),C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tmap_1)).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_52,plain,(
    m1_pre_topc('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_13355,plain,(
    ! [B_333,A_334] :
      ( l1_pre_topc(B_333)
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_13373,plain,
    ( l1_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_13355])).

tff(c_13390,plain,(
    l1_pre_topc('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13373])).

tff(c_16,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_13361,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_13355])).

tff(c_13380,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13361])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_76,plain,(
    ! [B_83,A_84] :
      ( l1_pre_topc(B_83)
      | ~ m1_pre_topc(B_83,A_84)
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_85,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_76])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_85])).

tff(c_56,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_76])).

tff(c_107,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_88])).

tff(c_44,plain,
    ( ~ r1_tsep_1('#skF_7','#skF_4')
    | ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_75,plain,(
    ~ r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_48,plain,(
    m1_pre_topc('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_1904,plain,(
    ! [A_211,C_212,B_213] :
      ( k1_tsep_1(A_211,C_212,B_213) = k1_tsep_1(A_211,B_213,C_212)
      | ~ m1_pre_topc(C_212,A_211)
      | v2_struct_0(C_212)
      | ~ m1_pre_topc(B_213,A_211)
      | v2_struct_0(B_213)
      | ~ l1_pre_topc(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1912,plain,(
    ! [B_213] :
      ( k1_tsep_1('#skF_3',B_213,'#skF_4') = k1_tsep_1('#skF_3','#skF_4',B_213)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_213,'#skF_3')
      | v2_struct_0(B_213)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_1904])).

tff(c_1928,plain,(
    ! [B_213] :
      ( k1_tsep_1('#skF_3',B_213,'#skF_4') = k1_tsep_1('#skF_3','#skF_4',B_213)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_213,'#skF_3')
      | v2_struct_0(B_213)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1912])).

tff(c_1950,plain,(
    ! [B_214] :
      ( k1_tsep_1('#skF_3',B_214,'#skF_4') = k1_tsep_1('#skF_3','#skF_4',B_214)
      | ~ m1_pre_topc(B_214,'#skF_3')
      | v2_struct_0(B_214) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1928])).

tff(c_1971,plain,
    ( k1_tsep_1('#skF_3','#skF_6','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_1950])).

tff(c_1995,plain,(
    k1_tsep_1('#skF_3','#skF_6','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1971])).

tff(c_26,plain,(
    ! [B_22,A_18,C_24] :
      ( m1_pre_topc(B_22,k1_tsep_1(A_18,B_22,C_24))
      | ~ m1_pre_topc(C_24,A_18)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_22,A_18)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2138,plain,
    ( m1_pre_topc('#skF_6',k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_26])).

tff(c_2154,plain,
    ( m1_pre_topc('#skF_6',k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_56,c_64,c_2138])).

tff(c_2155,plain,(
    m1_pre_topc('#skF_6',k1_tsep_1('#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_66,c_2154])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( m1_pre_topc(k1_tsep_1(A_4,B_5,C_6),A_4)
      | ~ m1_pre_topc(C_6,A_4)
      | v2_struct_0(C_6)
      | ~ m1_pre_topc(B_5,A_4)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2144,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_4])).

tff(c_2160,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_64,c_2144])).

tff(c_2161,plain,(
    m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_66,c_2160])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_pre_topc(k2_tsep_1(A_7,B_8,C_9),A_7)
      | ~ m1_pre_topc(C_9,A_7)
      | v2_struct_0(C_9)
      | ~ m1_pre_topc(B_8,A_7)
      | v2_struct_0(B_8)
      | ~ l1_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( ~ v2_struct_0(k1_tsep_1(A_4,B_5,C_6))
      | ~ m1_pre_topc(C_6,A_4)
      | v2_struct_0(C_6)
      | ~ m1_pre_topc(B_5,A_4)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2147,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1995,c_8])).

tff(c_2163,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_64,c_2147])).

tff(c_2164,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_66,c_2163])).

tff(c_46,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | r1_tsep_1('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_113,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_114,plain,(
    ! [B_85,A_86] :
      ( r1_tsep_1(B_85,A_86)
      | ~ r1_tsep_1(A_86,B_85)
      | ~ l1_struct_0(B_85)
      | ~ l1_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_117,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_113,c_114])).

tff(c_123,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_126,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_126])).

tff(c_132,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_843,plain,(
    ! [B_134,D_135,C_136,A_137] :
      ( r1_tsep_1(B_134,D_135)
      | ~ r1_tsep_1(D_135,C_136)
      | ~ m1_pre_topc(B_134,C_136)
      | ~ m1_pre_topc(D_135,A_137)
      | v2_struct_0(D_135)
      | ~ m1_pre_topc(C_136,A_137)
      | v2_struct_0(C_136)
      | ~ m1_pre_topc(B_134,A_137)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_847,plain,(
    ! [B_134,A_137] :
      ( r1_tsep_1(B_134,'#skF_5')
      | ~ m1_pre_topc(B_134,'#skF_7')
      | ~ m1_pre_topc('#skF_5',A_137)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_7',A_137)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc(B_134,A_137)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_113,c_843])).

tff(c_1652,plain,(
    ! [B_165,A_166] :
      ( r1_tsep_1(B_165,'#skF_5')
      | ~ m1_pre_topc(B_165,'#skF_7')
      | ~ m1_pre_topc('#skF_5',A_166)
      | ~ m1_pre_topc('#skF_7',A_166)
      | ~ m1_pre_topc(B_165,A_166)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_62,c_847])).

tff(c_1663,plain,(
    ! [B_165] :
      ( r1_tsep_1(B_165,'#skF_5')
      | ~ m1_pre_topc(B_165,'#skF_7')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_pre_topc(B_165,'#skF_3')
      | v2_struct_0(B_165)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_1652])).

tff(c_1681,plain,(
    ! [B_165] :
      ( r1_tsep_1(B_165,'#skF_5')
      | ~ m1_pre_topc(B_165,'#skF_7')
      | ~ m1_pre_topc(B_165,'#skF_3')
      | v2_struct_0(B_165)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_1663])).

tff(c_1719,plain,(
    ! [B_167] :
      ( r1_tsep_1(B_167,'#skF_5')
      | ~ m1_pre_topc(B_167,'#skF_7')
      | ~ m1_pre_topc(B_167,'#skF_3')
      | v2_struct_0(B_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1681])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( r1_tsep_1(B_17,A_16)
      | ~ r1_tsep_1(A_16,B_17)
      | ~ l1_struct_0(B_17)
      | ~ l1_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1745,plain,(
    ! [B_167] :
      ( r1_tsep_1('#skF_5',B_167)
      | ~ l1_struct_0('#skF_5')
      | ~ l1_struct_0(B_167)
      | ~ m1_pre_topc(B_167,'#skF_7')
      | ~ m1_pre_topc(B_167,'#skF_3')
      | v2_struct_0(B_167) ) ),
    inference(resolution,[status(thm)],[c_1719,c_24])).

tff(c_1785,plain,(
    ! [B_168] :
      ( r1_tsep_1('#skF_5',B_168)
      | ~ l1_struct_0(B_168)
      | ~ m1_pre_topc(B_168,'#skF_7')
      | ~ m1_pre_topc(B_168,'#skF_3')
      | v2_struct_0(B_168) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1745])).

tff(c_1798,plain,
    ( ~ l1_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1785,c_75])).

tff(c_1816,plain,
    ( ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_1798])).

tff(c_1817,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1816])).

tff(c_1820,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_1817])).

tff(c_1824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_1820])).

tff(c_1825,plain,(
    r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),k1_tsep_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_2181,plain,(
    ! [D_218,B_219,C_220,A_221] :
      ( r1_tsep_1(D_218,B_219)
      | ~ r1_tsep_1(D_218,C_220)
      | ~ m1_pre_topc(B_219,C_220)
      | ~ m1_pre_topc(D_218,A_221)
      | v2_struct_0(D_218)
      | ~ m1_pre_topc(C_220,A_221)
      | v2_struct_0(C_220)
      | ~ m1_pre_topc(B_219,A_221)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_2185,plain,(
    ! [B_219,A_221] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_219)
      | ~ m1_pre_topc(B_219,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_221)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_221)
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_219,A_221)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(resolution,[status(thm)],[c_1825,c_2181])).

tff(c_2191,plain,(
    ! [B_219,A_221] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_219)
      | ~ m1_pre_topc(B_219,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_221)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_221)
      | ~ m1_pre_topc(B_219,A_221)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2164,c_2185])).

tff(c_4830,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_2191])).

tff(c_14,plain,(
    ! [A_7,B_8,C_9] :
      ( ~ v2_struct_0(k2_tsep_1(A_7,B_8,C_9))
      | ~ m1_pre_topc(C_9,A_7)
      | v2_struct_0(C_9)
      | ~ m1_pre_topc(B_8,A_7)
      | v2_struct_0(B_8)
      | ~ l1_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_4833,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_3')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4830,c_14])).

tff(c_4836,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_52,c_4833])).

tff(c_4838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_54,c_4836])).

tff(c_4893,plain,(
    ! [B_275,A_276] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_275)
      | ~ m1_pre_topc(B_275,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_276)
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_276)
      | ~ m1_pre_topc(B_275,A_276)
      | v2_struct_0(B_275)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(splitRight,[status(thm)],[c_2191])).

tff(c_4899,plain,(
    ! [B_275] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_275)
      | ~ m1_pre_topc(B_275,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ m1_pre_topc(B_275,'#skF_3')
      | v2_struct_0(B_275)
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc('#skF_7','#skF_3')
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_4893])).

tff(c_4905,plain,(
    ! [B_275] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_275)
      | ~ m1_pre_topc(B_275,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_275,'#skF_3')
      | v2_struct_0(B_275)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_52,c_70,c_2161,c_4899])).

tff(c_13172,plain,(
    ! [B_329] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_329)
      | ~ m1_pre_topc(B_329,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_329,'#skF_3')
      | v2_struct_0(B_329) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_54,c_4905])).

tff(c_40,plain,(
    ! [A_40,C_52,D_54,B_48] :
      ( ~ r1_tsep_1(k2_tsep_1(A_40,C_52,D_54),B_48)
      | ~ m1_pre_topc(B_48,D_54)
      | r1_tsep_1(B_48,C_52)
      | ~ m1_pre_topc(D_54,A_40)
      | v2_struct_0(D_54)
      | ~ m1_pre_topc(C_52,A_40)
      | v2_struct_0(C_52)
      | ~ m1_pre_topc(B_48,A_40)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_13175,plain,(
    ! [B_329] :
      ( ~ m1_pre_topc(B_329,'#skF_7')
      | r1_tsep_1(B_329,'#skF_5')
      | ~ m1_pre_topc('#skF_7','#skF_3')
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_329,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_329,'#skF_3')
      | v2_struct_0(B_329) ) ),
    inference(resolution,[status(thm)],[c_13172,c_40])).

tff(c_13197,plain,(
    ! [B_329] :
      ( ~ m1_pre_topc(B_329,'#skF_7')
      | r1_tsep_1(B_329,'#skF_5')
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_329,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_329,'#skF_3')
      | v2_struct_0(B_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_52,c_13175])).

tff(c_13226,plain,(
    ! [B_330] :
      ( ~ m1_pre_topc(B_330,'#skF_7')
      | r1_tsep_1(B_330,'#skF_5')
      | ~ m1_pre_topc(B_330,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_330,'#skF_3')
      | v2_struct_0(B_330) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_54,c_13197])).

tff(c_13232,plain,
    ( ~ m1_pre_topc('#skF_6','#skF_7')
    | r1_tsep_1('#skF_6','#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2155,c_13226])).

tff(c_13255,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_13232])).

tff(c_13256,plain,(
    r1_tsep_1('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_13255])).

tff(c_13281,plain,
    ( r1_tsep_1('#skF_5','#skF_6')
    | ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_13256,c_24])).

tff(c_13296,plain,
    ( ~ l1_struct_0('#skF_5')
    | ~ l1_struct_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_13281])).

tff(c_13335,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_13296])).

tff(c_13338,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_13335])).

tff(c_13342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_13338])).

tff(c_13343,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_13296])).

tff(c_13348,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_13343])).

tff(c_13352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_13348])).

tff(c_13353,plain,(
    ~ r1_tsep_1('#skF_7','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_15994,plain,(
    ! [A_506,C_507,B_508] :
      ( k1_tsep_1(A_506,C_507,B_508) = k1_tsep_1(A_506,B_508,C_507)
      | ~ m1_pre_topc(C_507,A_506)
      | v2_struct_0(C_507)
      | ~ m1_pre_topc(B_508,A_506)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16002,plain,(
    ! [B_508] :
      ( k1_tsep_1('#skF_3',B_508,'#skF_4') = k1_tsep_1('#skF_3','#skF_4',B_508)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_508,'#skF_3')
      | v2_struct_0(B_508)
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_64,c_15994])).

tff(c_16018,plain,(
    ! [B_508] :
      ( k1_tsep_1('#skF_3',B_508,'#skF_4') = k1_tsep_1('#skF_3','#skF_4',B_508)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_508,'#skF_3')
      | v2_struct_0(B_508)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_16002])).

tff(c_16040,plain,(
    ! [B_509] :
      ( k1_tsep_1('#skF_3',B_509,'#skF_4') = k1_tsep_1('#skF_3','#skF_4',B_509)
      | ~ m1_pre_topc(B_509,'#skF_3')
      | v2_struct_0(B_509) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_16018])).

tff(c_16061,plain,
    ( k1_tsep_1('#skF_3','#skF_6','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_16040])).

tff(c_16085,plain,(
    k1_tsep_1('#skF_3','#skF_6','#skF_4') = k1_tsep_1('#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_16061])).

tff(c_16251,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16085,c_4])).

tff(c_16267,plain,
    ( m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_64,c_16251])).

tff(c_16268,plain,(
    m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_66,c_16267])).

tff(c_16257,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16085,c_8])).

tff(c_16273,plain,
    ( ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_56,c_64,c_16257])).

tff(c_16274,plain,(
    ~ v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_66,c_16273])).

tff(c_13364,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_13355])).

tff(c_13383,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13364])).

tff(c_13354,plain,(
    r1_tsep_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_13392,plain,(
    ! [B_335,A_336] :
      ( r1_tsep_1(B_335,A_336)
      | ~ r1_tsep_1(A_336,B_335)
      | ~ l1_struct_0(B_335)
      | ~ l1_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_13395,plain,
    ( r1_tsep_1('#skF_6','#skF_5')
    | ~ l1_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13354,c_13392])).

tff(c_13405,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_13395])).

tff(c_13409,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_13405])).

tff(c_13413,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13383,c_13409])).

tff(c_13415,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_13395])).

tff(c_13396,plain,(
    r1_tsep_1('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_13399,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13396,c_24])).

tff(c_13435,plain,
    ( r1_tsep_1('#skF_7','#skF_5')
    | ~ l1_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13415,c_13399])).

tff(c_13436,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_13435])).

tff(c_13439,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_16,c_13436])).

tff(c_13443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13390,c_13439])).

tff(c_13445,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_13435])).

tff(c_13753,plain,(
    ! [B_376,D_377,C_378,A_379] :
      ( r1_tsep_1(B_376,D_377)
      | ~ r1_tsep_1(C_378,D_377)
      | ~ m1_pre_topc(B_376,C_378)
      | ~ m1_pre_topc(D_377,A_379)
      | v2_struct_0(D_377)
      | ~ m1_pre_topc(C_378,A_379)
      | v2_struct_0(C_378)
      | ~ m1_pre_topc(B_376,A_379)
      | v2_struct_0(B_376)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_13759,plain,(
    ! [B_376,A_379] :
      ( r1_tsep_1(B_376,'#skF_7')
      | ~ m1_pre_topc(B_376,'#skF_5')
      | ~ m1_pre_topc('#skF_7',A_379)
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc('#skF_5',A_379)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_376,A_379)
      | v2_struct_0(B_376)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(resolution,[status(thm)],[c_13396,c_13753])).

tff(c_15643,plain,(
    ! [B_431,A_432] :
      ( r1_tsep_1(B_431,'#skF_7')
      | ~ m1_pre_topc(B_431,'#skF_5')
      | ~ m1_pre_topc('#skF_7',A_432)
      | ~ m1_pre_topc('#skF_5',A_432)
      | ~ m1_pre_topc(B_431,A_432)
      | v2_struct_0(B_431)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_54,c_13759])).

tff(c_15654,plain,(
    ! [B_431] :
      ( r1_tsep_1(B_431,'#skF_7')
      | ~ m1_pre_topc(B_431,'#skF_5')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | ~ m1_pre_topc(B_431,'#skF_3')
      | v2_struct_0(B_431)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_15643])).

tff(c_15672,plain,(
    ! [B_431] :
      ( r1_tsep_1(B_431,'#skF_7')
      | ~ m1_pre_topc(B_431,'#skF_5')
      | ~ m1_pre_topc(B_431,'#skF_3')
      | v2_struct_0(B_431)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_15654])).

tff(c_15710,plain,(
    ! [B_433] :
      ( r1_tsep_1(B_433,'#skF_7')
      | ~ m1_pre_topc(B_433,'#skF_5')
      | ~ m1_pre_topc(B_433,'#skF_3')
      | v2_struct_0(B_433) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_15672])).

tff(c_15736,plain,(
    ! [B_433] :
      ( r1_tsep_1('#skF_7',B_433)
      | ~ l1_struct_0('#skF_7')
      | ~ l1_struct_0(B_433)
      | ~ m1_pre_topc(B_433,'#skF_5')
      | ~ m1_pre_topc(B_433,'#skF_3')
      | v2_struct_0(B_433) ) ),
    inference(resolution,[status(thm)],[c_15710,c_24])).

tff(c_15821,plain,(
    ! [B_435] :
      ( r1_tsep_1('#skF_7',B_435)
      | ~ l1_struct_0(B_435)
      | ~ m1_pre_topc(B_435,'#skF_5')
      | ~ m1_pre_topc(B_435,'#skF_3')
      | v2_struct_0(B_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13445,c_15736])).

tff(c_15834,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_15821,c_13353])).

tff(c_15852,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_50,c_15834])).

tff(c_15853,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_15852])).

tff(c_15856,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_15853])).

tff(c_15860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13380,c_15856])).

tff(c_15861,plain,(
    r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),k1_tsep_1('#skF_3','#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16373,plain,(
    ! [B_518,D_519,C_520,A_521] :
      ( r1_tsep_1(B_518,D_519)
      | ~ r1_tsep_1(C_520,D_519)
      | ~ m1_pre_topc(B_518,C_520)
      | ~ m1_pre_topc(D_519,A_521)
      | v2_struct_0(D_519)
      | ~ m1_pre_topc(C_520,A_521)
      | v2_struct_0(C_520)
      | ~ m1_pre_topc(B_518,A_521)
      | v2_struct_0(B_518)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_16379,plain,(
    ! [B_518,A_521] :
      ( r1_tsep_1(B_518,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_518,k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_521)
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_521)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(B_518,A_521)
      | v2_struct_0(B_518)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(resolution,[status(thm)],[c_15861,c_16373])).

tff(c_16390,plain,(
    ! [B_518,A_521] :
      ( r1_tsep_1(B_518,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_518,k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_521)
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_521)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(B_518,A_521)
      | v2_struct_0(B_518)
      | ~ l1_pre_topc(A_521)
      | ~ v2_pre_topc(A_521)
      | v2_struct_0(A_521) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16274,c_16379])).

tff(c_19537,plain,(
    v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_16390])).

tff(c_19540,plain,
    ( ~ m1_pre_topc('#skF_7','#skF_3')
    | v2_struct_0('#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_19537,c_14])).

tff(c_19543,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_52,c_19540])).

tff(c_19545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_54,c_19543])).

tff(c_19547,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_16390])).

tff(c_16699,plain,(
    ! [D_528,B_529,C_530,A_531] :
      ( r1_tsep_1(D_528,B_529)
      | ~ r1_tsep_1(D_528,C_530)
      | ~ m1_pre_topc(B_529,C_530)
      | ~ m1_pre_topc(D_528,A_531)
      | v2_struct_0(D_528)
      | ~ m1_pre_topc(C_530,A_531)
      | v2_struct_0(C_530)
      | ~ m1_pre_topc(B_529,A_531)
      | v2_struct_0(B_529)
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_16705,plain,(
    ! [B_529,A_531] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_529)
      | ~ m1_pre_topc(B_529,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_531)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_531)
      | v2_struct_0(k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_529,A_531)
      | v2_struct_0(B_529)
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(resolution,[status(thm)],[c_15861,c_16699])).

tff(c_16716,plain,(
    ! [B_529,A_531] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_529)
      | ~ m1_pre_topc(B_529,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_531)
      | v2_struct_0(k2_tsep_1('#skF_3','#skF_5','#skF_7'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_531)
      | ~ m1_pre_topc(B_529,A_531)
      | v2_struct_0(B_529)
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16274,c_16705])).

tff(c_19908,plain,(
    ! [B_586,A_587] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_586)
      | ~ m1_pre_topc(B_586,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_3','#skF_5','#skF_7'),A_587)
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),A_587)
      | ~ m1_pre_topc(B_586,A_587)
      | v2_struct_0(B_586)
      | ~ l1_pre_topc(A_587)
      | ~ v2_pre_topc(A_587)
      | v2_struct_0(A_587) ) ),
    inference(negUnitSimplification,[status(thm)],[c_19547,c_16716])).

tff(c_19917,plain,(
    ! [B_586] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_586)
      | ~ m1_pre_topc(B_586,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(k1_tsep_1('#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ m1_pre_topc(B_586,'#skF_3')
      | v2_struct_0(B_586)
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc('#skF_7','#skF_3')
      | v2_struct_0('#skF_7')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_19908])).

tff(c_19926,plain,(
    ! [B_586] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_586)
      | ~ m1_pre_topc(B_586,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_586,'#skF_3')
      | v2_struct_0(B_586)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_60,c_52,c_70,c_16268,c_19917])).

tff(c_26001,plain,(
    ! [B_621] :
      ( r1_tsep_1(k2_tsep_1('#skF_3','#skF_5','#skF_7'),B_621)
      | ~ m1_pre_topc(B_621,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_621,'#skF_3')
      | v2_struct_0(B_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_54,c_19926])).

tff(c_42,plain,(
    ! [A_40,D_54,C_52,B_48] :
      ( ~ r1_tsep_1(k2_tsep_1(A_40,D_54,C_52),B_48)
      | ~ m1_pre_topc(B_48,D_54)
      | r1_tsep_1(B_48,C_52)
      | ~ m1_pre_topc(D_54,A_40)
      | v2_struct_0(D_54)
      | ~ m1_pre_topc(C_52,A_40)
      | v2_struct_0(C_52)
      | ~ m1_pre_topc(B_48,A_40)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_40)
      | ~ v2_pre_topc(A_40)
      | v2_struct_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_213])).

tff(c_26004,plain,(
    ! [B_621] :
      ( ~ m1_pre_topc(B_621,'#skF_5')
      | r1_tsep_1(B_621,'#skF_7')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_7','#skF_3')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_621,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_621,'#skF_3')
      | v2_struct_0(B_621) ) ),
    inference(resolution,[status(thm)],[c_26001,c_42])).

tff(c_26026,plain,(
    ! [B_621] :
      ( ~ m1_pre_topc(B_621,'#skF_5')
      | r1_tsep_1(B_621,'#skF_7')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_621,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_621,'#skF_3')
      | v2_struct_0(B_621) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_52,c_60,c_26004])).

tff(c_26055,plain,(
    ! [B_622] :
      ( ~ m1_pre_topc(B_622,'#skF_5')
      | r1_tsep_1(B_622,'#skF_7')
      | ~ m1_pre_topc(B_622,k1_tsep_1('#skF_3','#skF_4','#skF_6'))
      | ~ m1_pre_topc(B_622,'#skF_3')
      | v2_struct_0(B_622) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_54,c_62,c_26026])).

tff(c_26065,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | r1_tsep_1('#skF_4','#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_3')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_26055])).

tff(c_26088,plain,
    ( r1_tsep_1('#skF_4','#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_56,c_50,c_26065])).

tff(c_26089,plain,(
    r1_tsep_1('#skF_4','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_58,c_26088])).

tff(c_26110,plain,
    ( r1_tsep_1('#skF_7','#skF_4')
    | ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26089,c_24])).

tff(c_26125,plain,
    ( ~ l1_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_13353,c_26110])).

tff(c_26127,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_26125])).

tff(c_26130,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_26127])).

tff(c_26134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13380,c_26130])).

tff(c_26135,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_26125])).

tff(c_26139,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_16,c_26135])).

tff(c_26143,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13390,c_26139])).

%------------------------------------------------------------------------------
