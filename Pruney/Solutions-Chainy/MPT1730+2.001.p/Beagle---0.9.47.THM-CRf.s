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
% DateTime   : Thu Dec  3 10:26:46 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 990 expanded)
%              Number of leaves         :   26 ( 310 expanded)
%              Depth                    :   17
%              Number of atoms          :  637 (6044 expanded)
%              Number of equality atoms :   14 (  30 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_178,negated_conjecture,(
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
                   => ( ~ ( ~ r1_tsep_1(k1_tsep_1(A,B,C),D)
                          & r1_tsep_1(B,D)
                          & r1_tsep_1(C,D) )
                      & ~ ( ~ ( r1_tsep_1(B,D)
                              & r1_tsep_1(C,D) )
                          & r1_tsep_1(k1_tsep_1(A,B,C),D) )
                      & ~ ( ~ r1_tsep_1(D,k1_tsep_1(A,B,C))
                          & r1_tsep_1(D,B)
                          & r1_tsep_1(D,C) )
                      & ~ ( ~ ( r1_tsep_1(D,B)
                              & r1_tsep_1(D,C) )
                          & r1_tsep_1(D,k1_tsep_1(A,B,C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_112,axiom,(
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

tff(f_120,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_28,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_634,plain,(
    ! [B_149,A_150] :
      ( l1_pre_topc(B_149)
      | ~ m1_pre_topc(B_149,A_150)
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_640,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_634])).

tff(c_649,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_640])).

tff(c_8,plain,(
    ! [A_4] :
      ( l1_struct_0(A_4)
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_36,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_32,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_1128,plain,(
    ! [A_280,B_281,C_282] :
      ( m1_pre_topc(k1_tsep_1(A_280,B_281,C_282),A_280)
      | ~ m1_pre_topc(C_282,A_280)
      | v2_struct_0(C_282)
      | ~ m1_pre_topc(B_281,A_280)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_10,plain,(
    ! [B_7,A_5] :
      ( l1_pre_topc(B_7)
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1133,plain,(
    ! [A_283,B_284,C_285] :
      ( l1_pre_topc(k1_tsep_1(A_283,B_284,C_285))
      | ~ m1_pre_topc(C_285,A_283)
      | v2_struct_0(C_285)
      | ~ m1_pre_topc(B_284,A_283)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(resolution,[status(thm)],[c_1128,c_10])).

tff(c_119,plain,(
    ! [B_43,A_44] :
      ( l1_pre_topc(B_43)
      | ~ m1_pre_topc(B_43,A_44)
      | ~ l1_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_131,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_128,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_119])).

tff(c_137,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_128])).

tff(c_125,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_119])).

tff(c_134,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_46,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_117,plain,(
    r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_140,plain,(
    ! [B_51,A_52] :
      ( r1_tsep_1(B_51,A_52)
      | ~ r1_tsep_1(A_52,B_51)
      | ~ l1_struct_0(B_51)
      | ~ l1_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_143,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_140])).

tff(c_160,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_143])).

tff(c_163,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_163])).

tff(c_169,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_179,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_pre_topc(k1_tsep_1(A_66,B_67,C_68),A_66)
      | ~ m1_pre_topc(C_68,A_66)
      | v2_struct_0(C_68)
      | ~ m1_pre_topc(B_67,A_66)
      | v2_struct_0(B_67)
      | ~ l1_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_184,plain,(
    ! [A_69,B_70,C_71] :
      ( l1_pre_topc(k1_tsep_1(A_69,B_70,C_71))
      | ~ m1_pre_topc(C_71,A_69)
      | v2_struct_0(C_71)
      | ~ m1_pre_topc(B_70,A_69)
      | v2_struct_0(B_70)
      | ~ l1_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_179,c_10])).

tff(c_168,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_143])).

tff(c_171,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_175,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_171])).

tff(c_187,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_184,c_175])).

tff(c_190,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_190])).

tff(c_193,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_116,plain,
    ( ~ r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_218,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_193,c_116])).

tff(c_219,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_194,plain,(
    l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_18,plain,(
    ! [A_23,B_25] :
      ( r1_xboole_0(u1_struct_0(A_23),u1_struct_0(B_25))
      | ~ r1_tsep_1(A_23,B_25)
      | ~ l1_struct_0(B_25)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_22,plain,(
    ! [A_26,B_27,C_28] :
      ( v1_pre_topc(k1_tsep_1(A_26,B_27,C_28))
      | ~ m1_pre_topc(C_28,A_26)
      | v2_struct_0(C_28)
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_20,plain,(
    ! [A_26,B_27,C_28] :
      ( m1_pre_topc(k1_tsep_1(A_26,B_27,C_28),A_26)
      | ~ m1_pre_topc(C_28,A_26)
      | v2_struct_0(C_28)
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_221,plain,(
    ! [A_88,B_89,C_90] :
      ( u1_struct_0(k1_tsep_1(A_88,B_89,C_90)) = k2_xboole_0(u1_struct_0(B_89),u1_struct_0(C_90))
      | ~ m1_pre_topc(k1_tsep_1(A_88,B_89,C_90),A_88)
      | ~ v1_pre_topc(k1_tsep_1(A_88,B_89,C_90))
      | v2_struct_0(k1_tsep_1(A_88,B_89,C_90))
      | ~ m1_pre_topc(C_90,A_88)
      | v2_struct_0(C_90)
      | ~ m1_pre_topc(B_89,A_88)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_225,plain,(
    ! [A_91,B_92,C_93] :
      ( u1_struct_0(k1_tsep_1(A_91,B_92,C_93)) = k2_xboole_0(u1_struct_0(B_92),u1_struct_0(C_93))
      | ~ v1_pre_topc(k1_tsep_1(A_91,B_92,C_93))
      | v2_struct_0(k1_tsep_1(A_91,B_92,C_93))
      | ~ m1_pre_topc(C_93,A_91)
      | v2_struct_0(C_93)
      | ~ m1_pre_topc(B_92,A_91)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_20,c_221])).

tff(c_24,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ v2_struct_0(k1_tsep_1(A_26,B_27,C_28))
      | ~ m1_pre_topc(C_28,A_26)
      | v2_struct_0(C_28)
      | ~ m1_pre_topc(B_27,A_26)
      | v2_struct_0(B_27)
      | ~ l1_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_285,plain,(
    ! [A_94,B_95,C_96] :
      ( u1_struct_0(k1_tsep_1(A_94,B_95,C_96)) = k2_xboole_0(u1_struct_0(B_95),u1_struct_0(C_96))
      | ~ v1_pre_topc(k1_tsep_1(A_94,B_95,C_96))
      | ~ m1_pre_topc(C_96,A_94)
      | v2_struct_0(C_96)
      | ~ m1_pre_topc(B_95,A_94)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_225,c_24])).

tff(c_289,plain,(
    ! [A_97,B_98,C_99] :
      ( u1_struct_0(k1_tsep_1(A_97,B_98,C_99)) = k2_xboole_0(u1_struct_0(B_98),u1_struct_0(C_99))
      | ~ m1_pre_topc(C_99,A_97)
      | v2_struct_0(C_99)
      | ~ m1_pre_topc(B_98,A_97)
      | v2_struct_0(B_98)
      | ~ l1_pre_topc(A_97)
      | v2_struct_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_22,c_285])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_xboole_0(A_1,B_2)
      | ~ r1_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_354,plain,(
    ! [A_104,B_105,A_106,C_107] :
      ( r1_xboole_0(A_104,u1_struct_0(B_105))
      | ~ r1_xboole_0(A_104,u1_struct_0(k1_tsep_1(A_106,B_105,C_107)))
      | ~ m1_pre_topc(C_107,A_106)
      | v2_struct_0(C_107)
      | ~ m1_pre_topc(B_105,A_106)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_6])).

tff(c_380,plain,(
    ! [A_112,B_113,C_114,A_115] :
      ( r1_xboole_0(u1_struct_0(A_112),u1_struct_0(B_113))
      | ~ m1_pre_topc(C_114,A_115)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_113,A_115)
      | v2_struct_0(B_113)
      | ~ l1_pre_topc(A_115)
      | v2_struct_0(A_115)
      | ~ r1_tsep_1(A_112,k1_tsep_1(A_115,B_113,C_114))
      | ~ l1_struct_0(k1_tsep_1(A_115,B_113,C_114))
      | ~ l1_struct_0(A_112) ) ),
    inference(resolution,[status(thm)],[c_18,c_354])).

tff(c_382,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_380])).

tff(c_385,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_194,c_40,c_36,c_32,c_382])).

tff(c_386,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_385])).

tff(c_16,plain,(
    ! [A_23,B_25] :
      ( r1_tsep_1(A_23,B_25)
      | ~ r1_xboole_0(u1_struct_0(A_23),u1_struct_0(B_25))
      | ~ l1_struct_0(B_25)
      | ~ l1_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_389,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_386,c_16])).

tff(c_392,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_389])).

tff(c_393,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_392])).

tff(c_396,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_396])).

tff(c_402,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_26,plain,(
    ! [B_30,A_29] :
      ( r1_tsep_1(B_30,A_29)
      | ~ r1_tsep_1(A_29,B_30)
      | ~ l1_struct_0(B_30)
      | ~ l1_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_404,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_402,c_26])).

tff(c_407,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_404])).

tff(c_408,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_407])).

tff(c_411,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_408])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_411])).

tff(c_416,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_407])).

tff(c_401,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_425,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_401])).

tff(c_426,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_425])).

tff(c_427,plain,(
    ! [A_120,B_121,C_122] :
      ( u1_struct_0(k1_tsep_1(A_120,B_121,C_122)) = k2_xboole_0(u1_struct_0(B_121),u1_struct_0(C_122))
      | ~ m1_pre_topc(k1_tsep_1(A_120,B_121,C_122),A_120)
      | ~ v1_pre_topc(k1_tsep_1(A_120,B_121,C_122))
      | v2_struct_0(k1_tsep_1(A_120,B_121,C_122))
      | ~ m1_pre_topc(C_122,A_120)
      | v2_struct_0(C_122)
      | ~ m1_pre_topc(B_121,A_120)
      | v2_struct_0(B_121)
      | ~ l1_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_431,plain,(
    ! [A_123,B_124,C_125] :
      ( u1_struct_0(k1_tsep_1(A_123,B_124,C_125)) = k2_xboole_0(u1_struct_0(B_124),u1_struct_0(C_125))
      | ~ v1_pre_topc(k1_tsep_1(A_123,B_124,C_125))
      | v2_struct_0(k1_tsep_1(A_123,B_124,C_125))
      | ~ m1_pre_topc(C_125,A_123)
      | v2_struct_0(C_125)
      | ~ m1_pre_topc(B_124,A_123)
      | v2_struct_0(B_124)
      | ~ l1_pre_topc(A_123)
      | v2_struct_0(A_123) ) ),
    inference(resolution,[status(thm)],[c_20,c_427])).

tff(c_491,plain,(
    ! [A_126,B_127,C_128] :
      ( u1_struct_0(k1_tsep_1(A_126,B_127,C_128)) = k2_xboole_0(u1_struct_0(B_127),u1_struct_0(C_128))
      | ~ v1_pre_topc(k1_tsep_1(A_126,B_127,C_128))
      | ~ m1_pre_topc(C_128,A_126)
      | v2_struct_0(C_128)
      | ~ m1_pre_topc(B_127,A_126)
      | v2_struct_0(B_127)
      | ~ l1_pre_topc(A_126)
      | v2_struct_0(A_126) ) ),
    inference(resolution,[status(thm)],[c_431,c_24])).

tff(c_495,plain,(
    ! [A_129,B_130,C_131] :
      ( u1_struct_0(k1_tsep_1(A_129,B_130,C_131)) = k2_xboole_0(u1_struct_0(B_130),u1_struct_0(C_131))
      | ~ m1_pre_topc(C_131,A_129)
      | v2_struct_0(C_131)
      | ~ m1_pre_topc(B_130,A_129)
      | v2_struct_0(B_130)
      | ~ l1_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(resolution,[status(thm)],[c_22,c_491])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_551,plain,(
    ! [A_132,C_133,A_134,B_135] :
      ( r1_xboole_0(A_132,u1_struct_0(C_133))
      | ~ r1_xboole_0(A_132,u1_struct_0(k1_tsep_1(A_134,B_135,C_133)))
      | ~ m1_pre_topc(C_133,A_134)
      | v2_struct_0(C_133)
      | ~ m1_pre_topc(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_4])).

tff(c_586,plain,(
    ! [A_144,C_145,A_146,B_147] :
      ( r1_xboole_0(u1_struct_0(A_144),u1_struct_0(C_145))
      | ~ m1_pre_topc(C_145,A_146)
      | v2_struct_0(C_145)
      | ~ m1_pre_topc(B_147,A_146)
      | v2_struct_0(B_147)
      | ~ l1_pre_topc(A_146)
      | v2_struct_0(A_146)
      | ~ r1_tsep_1(A_144,k1_tsep_1(A_146,B_147,C_145))
      | ~ l1_struct_0(k1_tsep_1(A_146,B_147,C_145))
      | ~ l1_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_18,c_551])).

tff(c_588,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_586])).

tff(c_591,plain,
    ( r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_194,c_40,c_36,c_32,c_588])).

tff(c_592,plain,(
    r1_xboole_0(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_591])).

tff(c_595,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_592,c_16])).

tff(c_598,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_595])).

tff(c_599,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_598])).

tff(c_602,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_599])).

tff(c_606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_602])).

tff(c_608,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_598])).

tff(c_607,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_598])).

tff(c_610,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_607,c_26])).

tff(c_613,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_608,c_610])).

tff(c_615,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_426,c_613])).

tff(c_616,plain,(
    ~ r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_617,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_425])).

tff(c_619,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_617,c_26])).

tff(c_622,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_619])).

tff(c_623,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_616,c_622])).

tff(c_626,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_623])).

tff(c_630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_626])).

tff(c_632,plain,(
    ~ r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_643,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_634])).

tff(c_652,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_643])).

tff(c_1032,plain,(
    ! [A_248,B_249,C_250] :
      ( m1_pre_topc(k1_tsep_1(A_248,B_249,C_250),A_248)
      | ~ m1_pre_topc(C_250,A_248)
      | v2_struct_0(C_250)
      | ~ m1_pre_topc(B_249,A_248)
      | v2_struct_0(B_249)
      | ~ l1_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1037,plain,(
    ! [A_251,B_252,C_253] :
      ( l1_pre_topc(k1_tsep_1(A_251,B_252,C_253))
      | ~ m1_pre_topc(C_253,A_251)
      | v2_struct_0(C_253)
      | ~ m1_pre_topc(B_252,A_251)
      | v2_struct_0(B_252)
      | ~ l1_pre_topc(A_251)
      | v2_struct_0(A_251) ) ),
    inference(resolution,[status(thm)],[c_1032,c_10])).

tff(c_60,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_2')
    | r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_653,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_60])).

tff(c_654,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_653])).

tff(c_657,plain,(
    ! [B_157,A_158] :
      ( r1_tsep_1(B_157,A_158)
      | ~ r1_tsep_1(A_158,B_157)
      | ~ l1_struct_0(B_157)
      | ~ l1_struct_0(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_660,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_654,c_657])).

tff(c_661,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_664,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_661])).

tff(c_668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_664])).

tff(c_670,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_637,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_634])).

tff(c_646,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_637])).

tff(c_728,plain,(
    ! [A_172,B_173,C_174] :
      ( m1_pre_topc(k1_tsep_1(A_172,B_173,C_174),A_172)
      | ~ m1_pre_topc(C_174,A_172)
      | v2_struct_0(C_174)
      | ~ m1_pre_topc(B_173,A_172)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_732,plain,(
    ! [A_172,B_173,C_174] :
      ( l1_pre_topc(k1_tsep_1(A_172,B_173,C_174))
      | ~ m1_pre_topc(C_174,A_172)
      | v2_struct_0(C_174)
      | ~ m1_pre_topc(B_173,A_172)
      | v2_struct_0(B_173)
      | ~ l1_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(resolution,[status(thm)],[c_728,c_10])).

tff(c_669,plain,
    ( ~ l1_struct_0('#skF_2')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_673,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_669])).

tff(c_676,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_673])).

tff(c_680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_676])).

tff(c_682,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_669])).

tff(c_631,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_703,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_631])).

tff(c_705,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_703,c_26])).

tff(c_708,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_705])).

tff(c_711,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_714,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_711])).

tff(c_718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_714])).

tff(c_720,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_719,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_747,plain,(
    ! [A_182,B_183,C_184] :
      ( u1_struct_0(k1_tsep_1(A_182,B_183,C_184)) = k2_xboole_0(u1_struct_0(B_183),u1_struct_0(C_184))
      | ~ m1_pre_topc(k1_tsep_1(A_182,B_183,C_184),A_182)
      | ~ v1_pre_topc(k1_tsep_1(A_182,B_183,C_184))
      | v2_struct_0(k1_tsep_1(A_182,B_183,C_184))
      | ~ m1_pre_topc(C_184,A_182)
      | v2_struct_0(C_184)
      | ~ m1_pre_topc(B_183,A_182)
      | v2_struct_0(B_183)
      | ~ l1_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_751,plain,(
    ! [A_185,B_186,C_187] :
      ( u1_struct_0(k1_tsep_1(A_185,B_186,C_187)) = k2_xboole_0(u1_struct_0(B_186),u1_struct_0(C_187))
      | ~ v1_pre_topc(k1_tsep_1(A_185,B_186,C_187))
      | v2_struct_0(k1_tsep_1(A_185,B_186,C_187))
      | ~ m1_pre_topc(C_187,A_185)
      | v2_struct_0(C_187)
      | ~ m1_pre_topc(B_186,A_185)
      | v2_struct_0(B_186)
      | ~ l1_pre_topc(A_185)
      | v2_struct_0(A_185) ) ),
    inference(resolution,[status(thm)],[c_20,c_747])).

tff(c_811,plain,(
    ! [A_188,B_189,C_190] :
      ( u1_struct_0(k1_tsep_1(A_188,B_189,C_190)) = k2_xboole_0(u1_struct_0(B_189),u1_struct_0(C_190))
      | ~ v1_pre_topc(k1_tsep_1(A_188,B_189,C_190))
      | ~ m1_pre_topc(C_190,A_188)
      | v2_struct_0(C_190)
      | ~ m1_pre_topc(B_189,A_188)
      | v2_struct_0(B_189)
      | ~ l1_pre_topc(A_188)
      | v2_struct_0(A_188) ) ),
    inference(resolution,[status(thm)],[c_751,c_24])).

tff(c_815,plain,(
    ! [A_191,B_192,C_193] :
      ( u1_struct_0(k1_tsep_1(A_191,B_192,C_193)) = k2_xboole_0(u1_struct_0(B_192),u1_struct_0(C_193))
      | ~ m1_pre_topc(C_193,A_191)
      | v2_struct_0(C_193)
      | ~ m1_pre_topc(B_192,A_191)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(resolution,[status(thm)],[c_22,c_811])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( ~ r1_xboole_0(A_1,C_3)
      | ~ r1_xboole_0(A_1,B_2)
      | r1_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_889,plain,(
    ! [A_202,C_203,B_204,A_205] :
      ( ~ r1_xboole_0(A_202,u1_struct_0(C_203))
      | ~ r1_xboole_0(A_202,u1_struct_0(B_204))
      | r1_xboole_0(A_202,u1_struct_0(k1_tsep_1(A_205,B_204,C_203)))
      | ~ m1_pre_topc(C_203,A_205)
      | v2_struct_0(C_203)
      | ~ m1_pre_topc(B_204,A_205)
      | v2_struct_0(B_204)
      | ~ l1_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_2])).

tff(c_936,plain,(
    ! [A_230,A_231,B_232,C_233] :
      ( r1_tsep_1(A_230,k1_tsep_1(A_231,B_232,C_233))
      | ~ l1_struct_0(k1_tsep_1(A_231,B_232,C_233))
      | ~ l1_struct_0(A_230)
      | ~ r1_xboole_0(u1_struct_0(A_230),u1_struct_0(C_233))
      | ~ r1_xboole_0(u1_struct_0(A_230),u1_struct_0(B_232))
      | ~ m1_pre_topc(C_233,A_231)
      | v2_struct_0(C_233)
      | ~ m1_pre_topc(B_232,A_231)
      | v2_struct_0(B_232)
      | ~ l1_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_889,c_16])).

tff(c_948,plain,(
    ! [A_234,A_235,B_236,B_237] :
      ( r1_tsep_1(A_234,k1_tsep_1(A_235,B_236,B_237))
      | ~ l1_struct_0(k1_tsep_1(A_235,B_236,B_237))
      | ~ r1_xboole_0(u1_struct_0(A_234),u1_struct_0(B_236))
      | ~ m1_pre_topc(B_237,A_235)
      | v2_struct_0(B_237)
      | ~ m1_pre_topc(B_236,A_235)
      | v2_struct_0(B_236)
      | ~ l1_pre_topc(A_235)
      | v2_struct_0(A_235)
      | ~ r1_tsep_1(A_234,B_237)
      | ~ l1_struct_0(B_237)
      | ~ l1_struct_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_18,c_936])).

tff(c_960,plain,(
    ! [A_238,A_239,B_240,B_241] :
      ( r1_tsep_1(A_238,k1_tsep_1(A_239,B_240,B_241))
      | ~ l1_struct_0(k1_tsep_1(A_239,B_240,B_241))
      | ~ m1_pre_topc(B_241,A_239)
      | v2_struct_0(B_241)
      | ~ m1_pre_topc(B_240,A_239)
      | v2_struct_0(B_240)
      | ~ l1_pre_topc(A_239)
      | v2_struct_0(A_239)
      | ~ r1_tsep_1(A_238,B_241)
      | ~ l1_struct_0(B_241)
      | ~ r1_tsep_1(A_238,B_240)
      | ~ l1_struct_0(B_240)
      | ~ l1_struct_0(A_238) ) ),
    inference(resolution,[status(thm)],[c_18,c_948])).

tff(c_974,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_3')
    | ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_960,c_632])).

tff(c_982,plain,
    ( ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_682,c_654,c_720,c_719,c_40,c_36,c_32,c_974])).

tff(c_983,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_982])).

tff(c_987,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_983])).

tff(c_990,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_732,c_987])).

tff(c_993,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_990])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_993])).

tff(c_997,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_996,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_631])).

tff(c_998,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_996])).

tff(c_1002,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_998,c_26])).

tff(c_1005,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_1002])).

tff(c_1006,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_997,c_1005])).

tff(c_1009,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_1006])).

tff(c_1013,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_1009])).

tff(c_1014,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_996])).

tff(c_1017,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1014,c_26])).

tff(c_1020,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_1017])).

tff(c_1021,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_1020])).

tff(c_1025,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_1021])).

tff(c_1040,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1037,c_1025])).

tff(c_1043,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_1040])).

tff(c_1045,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_1043])).

tff(c_1047,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_1046,plain,
    ( r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_653])).

tff(c_1050,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1046])).

tff(c_1053,plain,(
    ! [B_260,A_261] :
      ( r1_tsep_1(B_260,A_261)
      | ~ r1_tsep_1(A_261,B_260)
      | ~ l1_struct_0(B_260)
      | ~ l1_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1057,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1050,c_1053])).

tff(c_1063,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1047,c_1057])).

tff(c_1064,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1063])).

tff(c_1067,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_1064])).

tff(c_1071,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_1067])).

tff(c_1072,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1063])).

tff(c_1085,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1072])).

tff(c_1089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_1085])).

tff(c_1090,plain,(
    r1_tsep_1(k1_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1046])).

tff(c_1094,plain,(
    ! [B_265,A_266] :
      ( r1_tsep_1(B_265,A_266)
      | ~ r1_tsep_1(A_266,B_265)
      | ~ l1_struct_0(B_265)
      | ~ l1_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1096,plain,
    ( r1_tsep_1('#skF_4',k1_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1090,c_1094])).

tff(c_1099,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_1096])).

tff(c_1100,plain,(
    ~ l1_struct_0(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1099])).

tff(c_1104,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_1100])).

tff(c_1136,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1133,c_1104])).

tff(c_1139,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_1136])).

tff(c_1141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_38,c_34,c_1139])).

tff(c_1142,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1099])).

tff(c_1146,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1142])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_649,c_1146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:21:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.82  
% 4.46/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.83  %$ r1_xboole_0 > r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.46/1.83  
% 4.46/1.83  %Foreground sorts:
% 4.46/1.83  
% 4.46/1.83  
% 4.46/1.83  %Background operators:
% 4.46/1.83  
% 4.46/1.83  
% 4.46/1.83  %Foreground operators:
% 4.46/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.46/1.83  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.46/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.46/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.46/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.46/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.46/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.46/1.83  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.46/1.83  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.46/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.46/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.46/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.46/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.46/1.83  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.46/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.46/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.46/1.83  
% 4.46/1.85  tff(f_178, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (((~((~r1_tsep_1(k1_tsep_1(A, B, C), D) & r1_tsep_1(B, D)) & r1_tsep_1(C, D)) & ~(~(r1_tsep_1(B, D) & r1_tsep_1(C, D)) & r1_tsep_1(k1_tsep_1(A, B, C), D))) & ~((~r1_tsep_1(D, k1_tsep_1(A, B, C)) & r1_tsep_1(D, B)) & r1_tsep_1(D, C))) & ~(~(r1_tsep_1(D, B) & r1_tsep_1(D, C)) & r1_tsep_1(D, k1_tsep_1(A, B, C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tmap_1)).
% 4.46/1.85  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.46/1.85  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.46/1.85  tff(f_112, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 4.46/1.85  tff(f_120, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 4.46/1.85  tff(f_90, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 4.46/1.85  tff(f_81, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 4.46/1.85  tff(f_41, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 4.46/1.85  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_28, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_634, plain, (![B_149, A_150]: (l1_pre_topc(B_149) | ~m1_pre_topc(B_149, A_150) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_640, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_634])).
% 4.46/1.85  tff(c_649, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_640])).
% 4.46/1.85  tff(c_8, plain, (![A_4]: (l1_struct_0(A_4) | ~l1_pre_topc(A_4))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.46/1.85  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_38, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_34, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_36, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_32, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_1128, plain, (![A_280, B_281, C_282]: (m1_pre_topc(k1_tsep_1(A_280, B_281, C_282), A_280) | ~m1_pre_topc(C_282, A_280) | v2_struct_0(C_282) | ~m1_pre_topc(B_281, A_280) | v2_struct_0(B_281) | ~l1_pre_topc(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_10, plain, (![B_7, A_5]: (l1_pre_topc(B_7) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_1133, plain, (![A_283, B_284, C_285]: (l1_pre_topc(k1_tsep_1(A_283, B_284, C_285)) | ~m1_pre_topc(C_285, A_283) | v2_struct_0(C_285) | ~m1_pre_topc(B_284, A_283) | v2_struct_0(B_284) | ~l1_pre_topc(A_283) | v2_struct_0(A_283))), inference(resolution, [status(thm)], [c_1128, c_10])).
% 4.46/1.85  tff(c_119, plain, (![B_43, A_44]: (l1_pre_topc(B_43) | ~m1_pre_topc(B_43, A_44) | ~l1_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.46/1.85  tff(c_122, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_119])).
% 4.46/1.85  tff(c_131, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_122])).
% 4.46/1.85  tff(c_128, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_119])).
% 4.46/1.85  tff(c_137, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_128])).
% 4.46/1.85  tff(c_125, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_119])).
% 4.46/1.85  tff(c_134, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_125])).
% 4.46/1.85  tff(c_46, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_117, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_46])).
% 4.46/1.85  tff(c_140, plain, (![B_51, A_52]: (r1_tsep_1(B_51, A_52) | ~r1_tsep_1(A_52, B_51) | ~l1_struct_0(B_51) | ~l1_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_143, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_117, c_140])).
% 4.46/1.85  tff(c_160, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_143])).
% 4.46/1.85  tff(c_163, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_160])).
% 4.46/1.85  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_163])).
% 4.46/1.85  tff(c_169, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_143])).
% 4.46/1.85  tff(c_179, plain, (![A_66, B_67, C_68]: (m1_pre_topc(k1_tsep_1(A_66, B_67, C_68), A_66) | ~m1_pre_topc(C_68, A_66) | v2_struct_0(C_68) | ~m1_pre_topc(B_67, A_66) | v2_struct_0(B_67) | ~l1_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_184, plain, (![A_69, B_70, C_71]: (l1_pre_topc(k1_tsep_1(A_69, B_70, C_71)) | ~m1_pre_topc(C_71, A_69) | v2_struct_0(C_71) | ~m1_pre_topc(B_70, A_69) | v2_struct_0(B_70) | ~l1_pre_topc(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_179, c_10])).
% 4.46/1.85  tff(c_168, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_143])).
% 4.46/1.85  tff(c_171, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_168])).
% 4.46/1.85  tff(c_175, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_171])).
% 4.46/1.85  tff(c_187, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_184, c_175])).
% 4.46/1.85  tff(c_190, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_187])).
% 4.46/1.85  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_190])).
% 4.46/1.85  tff(c_193, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_168])).
% 4.46/1.85  tff(c_116, plain, (~r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_218, plain, (~r1_tsep_1('#skF_3', '#skF_4') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_193, c_116])).
% 4.46/1.85  tff(c_219, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_218])).
% 4.46/1.85  tff(c_194, plain, (l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_168])).
% 4.46/1.85  tff(c_18, plain, (![A_23, B_25]: (r1_xboole_0(u1_struct_0(A_23), u1_struct_0(B_25)) | ~r1_tsep_1(A_23, B_25) | ~l1_struct_0(B_25) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.46/1.85  tff(c_22, plain, (![A_26, B_27, C_28]: (v1_pre_topc(k1_tsep_1(A_26, B_27, C_28)) | ~m1_pre_topc(C_28, A_26) | v2_struct_0(C_28) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_20, plain, (![A_26, B_27, C_28]: (m1_pre_topc(k1_tsep_1(A_26, B_27, C_28), A_26) | ~m1_pre_topc(C_28, A_26) | v2_struct_0(C_28) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_221, plain, (![A_88, B_89, C_90]: (u1_struct_0(k1_tsep_1(A_88, B_89, C_90))=k2_xboole_0(u1_struct_0(B_89), u1_struct_0(C_90)) | ~m1_pre_topc(k1_tsep_1(A_88, B_89, C_90), A_88) | ~v1_pre_topc(k1_tsep_1(A_88, B_89, C_90)) | v2_struct_0(k1_tsep_1(A_88, B_89, C_90)) | ~m1_pre_topc(C_90, A_88) | v2_struct_0(C_90) | ~m1_pre_topc(B_89, A_88) | v2_struct_0(B_89) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.46/1.85  tff(c_225, plain, (![A_91, B_92, C_93]: (u1_struct_0(k1_tsep_1(A_91, B_92, C_93))=k2_xboole_0(u1_struct_0(B_92), u1_struct_0(C_93)) | ~v1_pre_topc(k1_tsep_1(A_91, B_92, C_93)) | v2_struct_0(k1_tsep_1(A_91, B_92, C_93)) | ~m1_pre_topc(C_93, A_91) | v2_struct_0(C_93) | ~m1_pre_topc(B_92, A_91) | v2_struct_0(B_92) | ~l1_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_20, c_221])).
% 4.46/1.85  tff(c_24, plain, (![A_26, B_27, C_28]: (~v2_struct_0(k1_tsep_1(A_26, B_27, C_28)) | ~m1_pre_topc(C_28, A_26) | v2_struct_0(C_28) | ~m1_pre_topc(B_27, A_26) | v2_struct_0(B_27) | ~l1_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_285, plain, (![A_94, B_95, C_96]: (u1_struct_0(k1_tsep_1(A_94, B_95, C_96))=k2_xboole_0(u1_struct_0(B_95), u1_struct_0(C_96)) | ~v1_pre_topc(k1_tsep_1(A_94, B_95, C_96)) | ~m1_pre_topc(C_96, A_94) | v2_struct_0(C_96) | ~m1_pre_topc(B_95, A_94) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_225, c_24])).
% 4.46/1.85  tff(c_289, plain, (![A_97, B_98, C_99]: (u1_struct_0(k1_tsep_1(A_97, B_98, C_99))=k2_xboole_0(u1_struct_0(B_98), u1_struct_0(C_99)) | ~m1_pre_topc(C_99, A_97) | v2_struct_0(C_99) | ~m1_pre_topc(B_98, A_97) | v2_struct_0(B_98) | ~l1_pre_topc(A_97) | v2_struct_0(A_97))), inference(resolution, [status(thm)], [c_22, c_285])).
% 4.46/1.85  tff(c_6, plain, (![A_1, B_2, C_3]: (r1_xboole_0(A_1, B_2) | ~r1_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.85  tff(c_354, plain, (![A_104, B_105, A_106, C_107]: (r1_xboole_0(A_104, u1_struct_0(B_105)) | ~r1_xboole_0(A_104, u1_struct_0(k1_tsep_1(A_106, B_105, C_107))) | ~m1_pre_topc(C_107, A_106) | v2_struct_0(C_107) | ~m1_pre_topc(B_105, A_106) | v2_struct_0(B_105) | ~l1_pre_topc(A_106) | v2_struct_0(A_106))), inference(superposition, [status(thm), theory('equality')], [c_289, c_6])).
% 4.46/1.85  tff(c_380, plain, (![A_112, B_113, C_114, A_115]: (r1_xboole_0(u1_struct_0(A_112), u1_struct_0(B_113)) | ~m1_pre_topc(C_114, A_115) | v2_struct_0(C_114) | ~m1_pre_topc(B_113, A_115) | v2_struct_0(B_113) | ~l1_pre_topc(A_115) | v2_struct_0(A_115) | ~r1_tsep_1(A_112, k1_tsep_1(A_115, B_113, C_114)) | ~l1_struct_0(k1_tsep_1(A_115, B_113, C_114)) | ~l1_struct_0(A_112))), inference(resolution, [status(thm)], [c_18, c_354])).
% 4.46/1.85  tff(c_382, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_117, c_380])).
% 4.46/1.85  tff(c_385, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_194, c_40, c_36, c_32, c_382])).
% 4.46/1.85  tff(c_386, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_385])).
% 4.46/1.85  tff(c_16, plain, (![A_23, B_25]: (r1_tsep_1(A_23, B_25) | ~r1_xboole_0(u1_struct_0(A_23), u1_struct_0(B_25)) | ~l1_struct_0(B_25) | ~l1_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.46/1.85  tff(c_389, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_386, c_16])).
% 4.46/1.85  tff(c_392, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_389])).
% 4.46/1.85  tff(c_393, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_219, c_392])).
% 4.46/1.85  tff(c_396, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_393])).
% 4.46/1.85  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_396])).
% 4.46/1.85  tff(c_402, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_218])).
% 4.46/1.85  tff(c_26, plain, (![B_30, A_29]: (r1_tsep_1(B_30, A_29) | ~r1_tsep_1(A_29, B_30) | ~l1_struct_0(B_30) | ~l1_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_404, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_402, c_26])).
% 4.46/1.85  tff(c_407, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_404])).
% 4.46/1.85  tff(c_408, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_407])).
% 4.46/1.85  tff(c_411, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_408])).
% 4.46/1.85  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_411])).
% 4.46/1.85  tff(c_416, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_407])).
% 4.46/1.85  tff(c_401, plain, (~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_218])).
% 4.46/1.85  tff(c_425, plain, (~r1_tsep_1('#skF_4', '#skF_3') | ~r1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_416, c_401])).
% 4.46/1.85  tff(c_426, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_425])).
% 4.46/1.85  tff(c_427, plain, (![A_120, B_121, C_122]: (u1_struct_0(k1_tsep_1(A_120, B_121, C_122))=k2_xboole_0(u1_struct_0(B_121), u1_struct_0(C_122)) | ~m1_pre_topc(k1_tsep_1(A_120, B_121, C_122), A_120) | ~v1_pre_topc(k1_tsep_1(A_120, B_121, C_122)) | v2_struct_0(k1_tsep_1(A_120, B_121, C_122)) | ~m1_pre_topc(C_122, A_120) | v2_struct_0(C_122) | ~m1_pre_topc(B_121, A_120) | v2_struct_0(B_121) | ~l1_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.46/1.85  tff(c_431, plain, (![A_123, B_124, C_125]: (u1_struct_0(k1_tsep_1(A_123, B_124, C_125))=k2_xboole_0(u1_struct_0(B_124), u1_struct_0(C_125)) | ~v1_pre_topc(k1_tsep_1(A_123, B_124, C_125)) | v2_struct_0(k1_tsep_1(A_123, B_124, C_125)) | ~m1_pre_topc(C_125, A_123) | v2_struct_0(C_125) | ~m1_pre_topc(B_124, A_123) | v2_struct_0(B_124) | ~l1_pre_topc(A_123) | v2_struct_0(A_123))), inference(resolution, [status(thm)], [c_20, c_427])).
% 4.46/1.85  tff(c_491, plain, (![A_126, B_127, C_128]: (u1_struct_0(k1_tsep_1(A_126, B_127, C_128))=k2_xboole_0(u1_struct_0(B_127), u1_struct_0(C_128)) | ~v1_pre_topc(k1_tsep_1(A_126, B_127, C_128)) | ~m1_pre_topc(C_128, A_126) | v2_struct_0(C_128) | ~m1_pre_topc(B_127, A_126) | v2_struct_0(B_127) | ~l1_pre_topc(A_126) | v2_struct_0(A_126))), inference(resolution, [status(thm)], [c_431, c_24])).
% 4.46/1.85  tff(c_495, plain, (![A_129, B_130, C_131]: (u1_struct_0(k1_tsep_1(A_129, B_130, C_131))=k2_xboole_0(u1_struct_0(B_130), u1_struct_0(C_131)) | ~m1_pre_topc(C_131, A_129) | v2_struct_0(C_131) | ~m1_pre_topc(B_130, A_129) | v2_struct_0(B_130) | ~l1_pre_topc(A_129) | v2_struct_0(A_129))), inference(resolution, [status(thm)], [c_22, c_491])).
% 4.46/1.85  tff(c_4, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.85  tff(c_551, plain, (![A_132, C_133, A_134, B_135]: (r1_xboole_0(A_132, u1_struct_0(C_133)) | ~r1_xboole_0(A_132, u1_struct_0(k1_tsep_1(A_134, B_135, C_133))) | ~m1_pre_topc(C_133, A_134) | v2_struct_0(C_133) | ~m1_pre_topc(B_135, A_134) | v2_struct_0(B_135) | ~l1_pre_topc(A_134) | v2_struct_0(A_134))), inference(superposition, [status(thm), theory('equality')], [c_495, c_4])).
% 4.46/1.85  tff(c_586, plain, (![A_144, C_145, A_146, B_147]: (r1_xboole_0(u1_struct_0(A_144), u1_struct_0(C_145)) | ~m1_pre_topc(C_145, A_146) | v2_struct_0(C_145) | ~m1_pre_topc(B_147, A_146) | v2_struct_0(B_147) | ~l1_pre_topc(A_146) | v2_struct_0(A_146) | ~r1_tsep_1(A_144, k1_tsep_1(A_146, B_147, C_145)) | ~l1_struct_0(k1_tsep_1(A_146, B_147, C_145)) | ~l1_struct_0(A_144))), inference(resolution, [status(thm)], [c_18, c_551])).
% 4.46/1.85  tff(c_588, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_117, c_586])).
% 4.46/1.85  tff(c_591, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_194, c_40, c_36, c_32, c_588])).
% 4.46/1.85  tff(c_592, plain, (r1_xboole_0(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_591])).
% 4.46/1.85  tff(c_595, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_592, c_16])).
% 4.46/1.85  tff(c_598, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_595])).
% 4.46/1.85  tff(c_599, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_598])).
% 4.46/1.85  tff(c_602, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_599])).
% 4.46/1.85  tff(c_606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_602])).
% 4.46/1.85  tff(c_608, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_598])).
% 4.46/1.85  tff(c_607, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_598])).
% 4.46/1.85  tff(c_610, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_607, c_26])).
% 4.46/1.85  tff(c_613, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_608, c_610])).
% 4.46/1.85  tff(c_615, plain, $false, inference(negUnitSimplification, [status(thm)], [c_426, c_613])).
% 4.46/1.85  tff(c_616, plain, (~r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_425])).
% 4.46/1.85  tff(c_617, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_425])).
% 4.46/1.85  tff(c_619, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_617, c_26])).
% 4.46/1.85  tff(c_622, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_619])).
% 4.46/1.85  tff(c_623, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_616, c_622])).
% 4.46/1.85  tff(c_626, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_623])).
% 4.46/1.85  tff(c_630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_626])).
% 4.46/1.85  tff(c_632, plain, (~r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 4.46/1.85  tff(c_643, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_634])).
% 4.46/1.85  tff(c_652, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_643])).
% 4.46/1.85  tff(c_1032, plain, (![A_248, B_249, C_250]: (m1_pre_topc(k1_tsep_1(A_248, B_249, C_250), A_248) | ~m1_pre_topc(C_250, A_248) | v2_struct_0(C_250) | ~m1_pre_topc(B_249, A_248) | v2_struct_0(B_249) | ~l1_pre_topc(A_248) | v2_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_1037, plain, (![A_251, B_252, C_253]: (l1_pre_topc(k1_tsep_1(A_251, B_252, C_253)) | ~m1_pre_topc(C_253, A_251) | v2_struct_0(C_253) | ~m1_pre_topc(B_252, A_251) | v2_struct_0(B_252) | ~l1_pre_topc(A_251) | v2_struct_0(A_251))), inference(resolution, [status(thm)], [c_1032, c_10])).
% 4.46/1.85  tff(c_60, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_2') | r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_178])).
% 4.46/1.85  tff(c_653, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_632, c_60])).
% 4.46/1.85  tff(c_654, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_653])).
% 4.46/1.85  tff(c_657, plain, (![B_157, A_158]: (r1_tsep_1(B_157, A_158) | ~r1_tsep_1(A_158, B_157) | ~l1_struct_0(B_157) | ~l1_struct_0(A_158))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_660, plain, (r1_tsep_1('#skF_2', '#skF_4') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_654, c_657])).
% 4.46/1.85  tff(c_661, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_660])).
% 4.46/1.85  tff(c_664, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_661])).
% 4.46/1.85  tff(c_668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_649, c_664])).
% 4.46/1.85  tff(c_670, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_660])).
% 4.46/1.85  tff(c_637, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_634])).
% 4.46/1.85  tff(c_646, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_637])).
% 4.46/1.85  tff(c_728, plain, (![A_172, B_173, C_174]: (m1_pre_topc(k1_tsep_1(A_172, B_173, C_174), A_172) | ~m1_pre_topc(C_174, A_172) | v2_struct_0(C_174) | ~m1_pre_topc(B_173, A_172) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.46/1.85  tff(c_732, plain, (![A_172, B_173, C_174]: (l1_pre_topc(k1_tsep_1(A_172, B_173, C_174)) | ~m1_pre_topc(C_174, A_172) | v2_struct_0(C_174) | ~m1_pre_topc(B_173, A_172) | v2_struct_0(B_173) | ~l1_pre_topc(A_172) | v2_struct_0(A_172))), inference(resolution, [status(thm)], [c_728, c_10])).
% 4.46/1.85  tff(c_669, plain, (~l1_struct_0('#skF_2') | r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_660])).
% 4.46/1.85  tff(c_673, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_669])).
% 4.46/1.85  tff(c_676, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_673])).
% 4.46/1.85  tff(c_680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_676])).
% 4.46/1.85  tff(c_682, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_669])).
% 4.46/1.85  tff(c_631, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_46])).
% 4.46/1.85  tff(c_703, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_631])).
% 4.46/1.85  tff(c_705, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_703, c_26])).
% 4.46/1.85  tff(c_708, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_705])).
% 4.46/1.85  tff(c_711, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_708])).
% 4.46/1.85  tff(c_714, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_711])).
% 4.46/1.85  tff(c_718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_646, c_714])).
% 4.46/1.85  tff(c_720, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_708])).
% 4.46/1.85  tff(c_719, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_708])).
% 4.46/1.85  tff(c_747, plain, (![A_182, B_183, C_184]: (u1_struct_0(k1_tsep_1(A_182, B_183, C_184))=k2_xboole_0(u1_struct_0(B_183), u1_struct_0(C_184)) | ~m1_pre_topc(k1_tsep_1(A_182, B_183, C_184), A_182) | ~v1_pre_topc(k1_tsep_1(A_182, B_183, C_184)) | v2_struct_0(k1_tsep_1(A_182, B_183, C_184)) | ~m1_pre_topc(C_184, A_182) | v2_struct_0(C_184) | ~m1_pre_topc(B_183, A_182) | v2_struct_0(B_183) | ~l1_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.46/1.85  tff(c_751, plain, (![A_185, B_186, C_187]: (u1_struct_0(k1_tsep_1(A_185, B_186, C_187))=k2_xboole_0(u1_struct_0(B_186), u1_struct_0(C_187)) | ~v1_pre_topc(k1_tsep_1(A_185, B_186, C_187)) | v2_struct_0(k1_tsep_1(A_185, B_186, C_187)) | ~m1_pre_topc(C_187, A_185) | v2_struct_0(C_187) | ~m1_pre_topc(B_186, A_185) | v2_struct_0(B_186) | ~l1_pre_topc(A_185) | v2_struct_0(A_185))), inference(resolution, [status(thm)], [c_20, c_747])).
% 4.46/1.85  tff(c_811, plain, (![A_188, B_189, C_190]: (u1_struct_0(k1_tsep_1(A_188, B_189, C_190))=k2_xboole_0(u1_struct_0(B_189), u1_struct_0(C_190)) | ~v1_pre_topc(k1_tsep_1(A_188, B_189, C_190)) | ~m1_pre_topc(C_190, A_188) | v2_struct_0(C_190) | ~m1_pre_topc(B_189, A_188) | v2_struct_0(B_189) | ~l1_pre_topc(A_188) | v2_struct_0(A_188))), inference(resolution, [status(thm)], [c_751, c_24])).
% 4.46/1.85  tff(c_815, plain, (![A_191, B_192, C_193]: (u1_struct_0(k1_tsep_1(A_191, B_192, C_193))=k2_xboole_0(u1_struct_0(B_192), u1_struct_0(C_193)) | ~m1_pre_topc(C_193, A_191) | v2_struct_0(C_193) | ~m1_pre_topc(B_192, A_191) | v2_struct_0(B_192) | ~l1_pre_topc(A_191) | v2_struct_0(A_191))), inference(resolution, [status(thm)], [c_22, c_811])).
% 4.46/1.85  tff(c_2, plain, (![A_1, C_3, B_2]: (~r1_xboole_0(A_1, C_3) | ~r1_xboole_0(A_1, B_2) | r1_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.46/1.85  tff(c_889, plain, (![A_202, C_203, B_204, A_205]: (~r1_xboole_0(A_202, u1_struct_0(C_203)) | ~r1_xboole_0(A_202, u1_struct_0(B_204)) | r1_xboole_0(A_202, u1_struct_0(k1_tsep_1(A_205, B_204, C_203))) | ~m1_pre_topc(C_203, A_205) | v2_struct_0(C_203) | ~m1_pre_topc(B_204, A_205) | v2_struct_0(B_204) | ~l1_pre_topc(A_205) | v2_struct_0(A_205))), inference(superposition, [status(thm), theory('equality')], [c_815, c_2])).
% 4.46/1.85  tff(c_936, plain, (![A_230, A_231, B_232, C_233]: (r1_tsep_1(A_230, k1_tsep_1(A_231, B_232, C_233)) | ~l1_struct_0(k1_tsep_1(A_231, B_232, C_233)) | ~l1_struct_0(A_230) | ~r1_xboole_0(u1_struct_0(A_230), u1_struct_0(C_233)) | ~r1_xboole_0(u1_struct_0(A_230), u1_struct_0(B_232)) | ~m1_pre_topc(C_233, A_231) | v2_struct_0(C_233) | ~m1_pre_topc(B_232, A_231) | v2_struct_0(B_232) | ~l1_pre_topc(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_889, c_16])).
% 4.46/1.85  tff(c_948, plain, (![A_234, A_235, B_236, B_237]: (r1_tsep_1(A_234, k1_tsep_1(A_235, B_236, B_237)) | ~l1_struct_0(k1_tsep_1(A_235, B_236, B_237)) | ~r1_xboole_0(u1_struct_0(A_234), u1_struct_0(B_236)) | ~m1_pre_topc(B_237, A_235) | v2_struct_0(B_237) | ~m1_pre_topc(B_236, A_235) | v2_struct_0(B_236) | ~l1_pre_topc(A_235) | v2_struct_0(A_235) | ~r1_tsep_1(A_234, B_237) | ~l1_struct_0(B_237) | ~l1_struct_0(A_234))), inference(resolution, [status(thm)], [c_18, c_936])).
% 4.46/1.85  tff(c_960, plain, (![A_238, A_239, B_240, B_241]: (r1_tsep_1(A_238, k1_tsep_1(A_239, B_240, B_241)) | ~l1_struct_0(k1_tsep_1(A_239, B_240, B_241)) | ~m1_pre_topc(B_241, A_239) | v2_struct_0(B_241) | ~m1_pre_topc(B_240, A_239) | v2_struct_0(B_240) | ~l1_pre_topc(A_239) | v2_struct_0(A_239) | ~r1_tsep_1(A_238, B_241) | ~l1_struct_0(B_241) | ~r1_tsep_1(A_238, B_240) | ~l1_struct_0(B_240) | ~l1_struct_0(A_238))), inference(resolution, [status(thm)], [c_18, c_948])).
% 4.46/1.85  tff(c_974, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_3') | ~r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_960, c_632])).
% 4.46/1.85  tff(c_982, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_682, c_654, c_720, c_719, c_40, c_36, c_32, c_974])).
% 4.46/1.85  tff(c_983, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_982])).
% 4.46/1.85  tff(c_987, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_983])).
% 4.46/1.85  tff(c_990, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_732, c_987])).
% 4.46/1.85  tff(c_993, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_990])).
% 4.46/1.85  tff(c_995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_993])).
% 4.46/1.85  tff(c_997, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_631])).
% 4.46/1.85  tff(c_996, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_631])).
% 4.46/1.85  tff(c_998, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_996])).
% 4.46/1.85  tff(c_1002, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_998, c_26])).
% 4.46/1.85  tff(c_1005, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_1002])).
% 4.46/1.85  tff(c_1006, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_997, c_1005])).
% 4.46/1.85  tff(c_1009, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_8, c_1006])).
% 4.46/1.85  tff(c_1013, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_646, c_1009])).
% 4.46/1.85  tff(c_1014, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_996])).
% 4.46/1.85  tff(c_1017, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1014, c_26])).
% 4.46/1.85  tff(c_1020, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_670, c_1017])).
% 4.46/1.85  tff(c_1021, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_632, c_1020])).
% 4.46/1.85  tff(c_1025, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1021])).
% 4.46/1.85  tff(c_1040, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1037, c_1025])).
% 4.46/1.85  tff(c_1043, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_1040])).
% 4.46/1.85  tff(c_1045, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_1043])).
% 4.46/1.85  tff(c_1047, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_653])).
% 4.46/1.85  tff(c_1046, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_653])).
% 4.46/1.85  tff(c_1050, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_1046])).
% 4.46/1.85  tff(c_1053, plain, (![B_260, A_261]: (r1_tsep_1(B_260, A_261) | ~r1_tsep_1(A_261, B_260) | ~l1_struct_0(B_260) | ~l1_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_1057, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1050, c_1053])).
% 4.46/1.85  tff(c_1063, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1047, c_1057])).
% 4.46/1.85  tff(c_1064, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1063])).
% 4.46/1.85  tff(c_1067, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_8, c_1064])).
% 4.46/1.85  tff(c_1071, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_652, c_1067])).
% 4.46/1.85  tff(c_1072, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1063])).
% 4.46/1.85  tff(c_1085, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_1072])).
% 4.46/1.85  tff(c_1089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_649, c_1085])).
% 4.46/1.85  tff(c_1090, plain, (r1_tsep_1(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_1046])).
% 4.46/1.85  tff(c_1094, plain, (![B_265, A_266]: (r1_tsep_1(B_265, A_266) | ~r1_tsep_1(A_266, B_265) | ~l1_struct_0(B_265) | ~l1_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.46/1.85  tff(c_1096, plain, (r1_tsep_1('#skF_4', k1_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_1090, c_1094])).
% 4.46/1.85  tff(c_1099, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_632, c_1096])).
% 4.46/1.85  tff(c_1100, plain, (~l1_struct_0(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1099])).
% 4.46/1.85  tff(c_1104, plain, (~l1_pre_topc(k1_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_8, c_1100])).
% 4.46/1.85  tff(c_1136, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1133, c_1104])).
% 4.46/1.85  tff(c_1139, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_1136])).
% 4.46/1.85  tff(c_1141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_38, c_34, c_1139])).
% 4.46/1.85  tff(c_1142, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1099])).
% 4.46/1.85  tff(c_1146, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_8, c_1142])).
% 4.46/1.85  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_649, c_1146])).
% 4.46/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.46/1.85  
% 4.46/1.85  Inference rules
% 4.46/1.85  ----------------------
% 4.46/1.85  #Ref     : 0
% 4.46/1.85  #Sup     : 232
% 4.46/1.85  #Fact    : 0
% 4.46/1.85  #Define  : 0
% 4.46/1.85  #Split   : 17
% 4.46/1.85  #Chain   : 0
% 4.46/1.85  #Close   : 0
% 4.46/1.85  
% 4.46/1.85  Ordering : KBO
% 4.46/1.85  
% 4.46/1.85  Simplification rules
% 4.46/1.85  ----------------------
% 4.46/1.85  #Subsume      : 32
% 4.46/1.85  #Demod        : 112
% 4.46/1.85  #Tautology    : 77
% 4.46/1.85  #SimpNegUnit  : 26
% 4.46/1.85  #BackRed      : 0
% 4.46/1.85  
% 4.46/1.85  #Partial instantiations: 0
% 4.46/1.85  #Strategies tried      : 1
% 4.46/1.85  
% 4.46/1.85  Timing (in seconds)
% 4.46/1.85  ----------------------
% 4.46/1.85  Preprocessing        : 0.38
% 4.46/1.85  Parsing              : 0.19
% 4.46/1.86  CNF conversion       : 0.03
% 4.46/1.86  Main loop            : 0.59
% 4.46/1.86  Inferencing          : 0.22
% 4.46/1.86  Reduction            : 0.14
% 4.46/1.86  Demodulation         : 0.09
% 4.46/1.86  BG Simplification    : 0.04
% 4.46/1.86  Subsumption          : 0.16
% 4.46/1.86  Abstraction          : 0.03
% 4.46/1.86  MUC search           : 0.00
% 4.46/1.86  Cooper               : 0.00
% 4.46/1.86  Total                : 1.04
% 4.46/1.86  Index Insertion      : 0.00
% 4.46/1.86  Index Deletion       : 0.00
% 4.46/1.86  Index Matching       : 0.00
% 4.46/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
