%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:45 EST 2020

% Result     : Theorem 9.46s
% Output     : CNFRefutation 10.07s
% Verified   : 
% Statistics : Number of formulae       :  412 (3898 expanded)
%              Number of leaves         :   24 (1443 expanded)
%              Depth                    :   27
%              Number of atoms          : 2264 (32119 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_237,negated_conjecture,(
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
                         => ( ~ r1_tsep_1(k2_tsep_1(A,D,C),B)
                            & ~ r1_tsep_1(k2_tsep_1(A,C,D),B) ) )
                        & ( m1_pre_topc(C,D)
                         => ( ~ r1_tsep_1(k2_tsep_1(A,B,D),C)
                            & ~ r1_tsep_1(k2_tsep_1(A,D,B),C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tmap_1)).

tff(f_58,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_156,axiom,(
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
             => ( ~ r1_tsep_1(B,C)
               => ( m1_pre_topc(k2_tsep_1(A,B,C),B)
                  & m1_pre_topc(k2_tsep_1(A,B,C),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

tff(f_192,axiom,(
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
                       => m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,D,C)) )
                      & ( m1_pre_topc(C,D)
                       => m1_pre_topc(k2_tsep_1(A,B,C),k2_tsep_1(A,B,D)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).

tff(f_130,axiom,(
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
                   => ( ( ~ r1_tsep_1(C,D)
                        & ~ r1_tsep_1(D,C) )
                      | ( r1_tsep_1(B,D)
                        & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_93,axiom,(
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
             => ( m1_pre_topc(B,C)
               => ( ~ r1_tsep_1(B,C)
                  & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_44,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( m1_pre_topc(k2_tsep_1(A_5,B_6,C_7),A_5)
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ m1_pre_topc(B_6,A_5)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_28,plain,(
    ! [A_32,B_36,C_38] :
      ( m1_pre_topc(k2_tsep_1(A_32,B_36,C_38),B_36)
      | r1_tsep_1(B_36,C_38)
      | ~ m1_pre_topc(C_38,A_32)
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_36,A_32)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_32,plain,(
    ! [A_39,B_47,C_51,D_53] :
      ( m1_pre_topc(k2_tsep_1(A_39,B_47,C_51),k2_tsep_1(A_39,D_53,C_51))
      | ~ m1_pre_topc(B_47,D_53)
      | r1_tsep_1(B_47,C_51)
      | ~ m1_pre_topc(D_53,A_39)
      | v2_struct_0(D_53)
      | ~ m1_pre_topc(C_51,A_39)
      | v2_struct_0(C_51)
      | ~ m1_pre_topc(B_47,A_39)
      | v2_struct_0(B_47)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_34,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_26,plain,(
    ! [A_32,B_36,C_38] :
      ( m1_pre_topc(k2_tsep_1(A_32,B_36,C_38),C_38)
      | r1_tsep_1(B_36,C_38)
      | ~ m1_pre_topc(C_38,A_32)
      | v2_struct_0(C_38)
      | ~ m1_pre_topc(B_36,A_32)
      | v2_struct_0(B_36)
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    ! [A_39,B_47,C_51,D_53] :
      ( m1_pre_topc(k2_tsep_1(A_39,B_47,C_51),k2_tsep_1(A_39,B_47,D_53))
      | ~ m1_pre_topc(C_51,D_53)
      | r1_tsep_1(B_47,C_51)
      | ~ m1_pre_topc(D_53,A_39)
      | v2_struct_0(D_53)
      | ~ m1_pre_topc(C_51,A_39)
      | v2_struct_0(C_51)
      | ~ m1_pre_topc(B_47,A_39)
      | v2_struct_0(B_47)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_56,plain,
    ( m1_pre_topc('#skF_2','#skF_4')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_90,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_197,plain,(
    ! [C_114,D_115,B_116,A_117] :
      ( ~ r1_tsep_1(C_114,D_115)
      | r1_tsep_1(D_115,B_116)
      | ~ m1_pre_topc(B_116,C_114)
      | ~ m1_pre_topc(D_115,A_117)
      | v2_struct_0(D_115)
      | ~ m1_pre_topc(C_114,A_117)
      | v2_struct_0(C_114)
      | ~ m1_pre_topc(B_116,A_117)
      | v2_struct_0(B_116)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_201,plain,(
    ! [B_116,A_117] :
      ( r1_tsep_1('#skF_3',B_116)
      | ~ m1_pre_topc(B_116,k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_117)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_117)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_116,A_117)
      | v2_struct_0(B_116)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_90,c_197])).

tff(c_207,plain,(
    ! [B_116,A_117] :
      ( r1_tsep_1('#skF_3',B_116)
      | ~ m1_pre_topc(B_116,k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_117)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_117)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_116,A_117)
      | v2_struct_0(B_116)
      | ~ l1_pre_topc(A_117)
      | ~ v2_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_201])).

tff(c_219,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( ~ v2_struct_0(k2_tsep_1(A_5,B_6,C_7))
      | ~ m1_pre_topc(C_7,A_5)
      | v2_struct_0(C_7)
      | ~ m1_pre_topc(B_6,A_5)
      | v2_struct_0(B_6)
      | ~ l1_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_222,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_219,c_10])).

tff(c_225,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_36,c_222])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_225])).

tff(c_229,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_208,plain,(
    ! [C_118,D_119,B_120,A_121] :
      ( ~ r1_tsep_1(C_118,D_119)
      | r1_tsep_1(B_120,D_119)
      | ~ m1_pre_topc(B_120,C_118)
      | ~ m1_pre_topc(D_119,A_121)
      | v2_struct_0(D_119)
      | ~ m1_pre_topc(C_118,A_121)
      | v2_struct_0(C_118)
      | ~ m1_pre_topc(B_120,A_121)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_212,plain,(
    ! [B_120,A_121] :
      ( r1_tsep_1(B_120,'#skF_3')
      | ~ m1_pre_topc(B_120,k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_121)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_121)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_120,A_121)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(resolution,[status(thm)],[c_90,c_208])).

tff(c_218,plain,(
    ! [B_120,A_121] :
      ( r1_tsep_1(B_120,'#skF_3')
      | ~ m1_pre_topc(B_120,k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_121)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_121)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc(B_120,A_121)
      | v2_struct_0(B_120)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121)
      | v2_struct_0(A_121) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_212])).

tff(c_262,plain,(
    ! [B_128,A_129] :
      ( r1_tsep_1(B_128,'#skF_3')
      | ~ m1_pre_topc(B_128,k2_tsep_1('#skF_1','#skF_2','#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_129)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_129)
      | ~ m1_pre_topc(B_128,A_129)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(negUnitSimplification,[status(thm)],[c_229,c_218])).

tff(c_265,plain,(
    ! [C_51,A_129] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2',C_51),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_129)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_129)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_51),A_129)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_51))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(C_51,'#skF_4')
      | r1_tsep_1('#skF_2',C_51)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_51,'#skF_1')
      | v2_struct_0(C_51)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_262])).

tff(c_277,plain,(
    ! [C_51,A_129] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2',C_51),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_129)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_129)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_51),A_129)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_51))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(C_51,'#skF_4')
      | r1_tsep_1('#skF_2',C_51)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_51,'#skF_1')
      | v2_struct_0(C_51)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_36,c_265])).

tff(c_917,plain,(
    ! [C_165,A_166] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2',C_165),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_166)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_4'),A_166)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_165),A_166)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_165))
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166)
      | ~ m1_pre_topc(C_165,'#skF_4')
      | r1_tsep_1('#skF_2',C_165)
      | ~ m1_pre_topc(C_165,'#skF_1')
      | v2_struct_0(C_165) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_277])).

tff(c_932,plain,(
    ! [C_165] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2',C_165),'#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_165),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_165))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_165,'#skF_4')
      | r1_tsep_1('#skF_2',C_165)
      | ~ m1_pre_topc(C_165,'#skF_1')
      | v2_struct_0(C_165)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_917])).

tff(c_951,plain,(
    ! [C_165] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2',C_165),'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_165),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_165))
      | ~ m1_pre_topc(C_165,'#skF_4')
      | r1_tsep_1('#skF_2',C_165)
      | ~ m1_pre_topc(C_165,'#skF_1')
      | v2_struct_0(C_165)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_36,c_50,c_40,c_932])).

tff(c_953,plain,(
    ! [C_167] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2',C_167),'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_167),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_167))
      | ~ m1_pre_topc(C_167,'#skF_4')
      | r1_tsep_1('#skF_2',C_167)
      | ~ m1_pre_topc(C_167,'#skF_1')
      | v2_struct_0(C_167) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_951])).

tff(c_16,plain,(
    ! [B_14,C_16,A_10] :
      ( ~ r1_tsep_1(B_14,C_16)
      | ~ m1_pre_topc(B_14,C_16)
      | ~ m1_pre_topc(C_16,A_10)
      | v2_struct_0(C_16)
      | ~ m1_pre_topc(B_14,A_10)
      | v2_struct_0(B_14)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_963,plain,(
    ! [C_167,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_167),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_10)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_167),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_167),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_167))
      | ~ m1_pre_topc(C_167,'#skF_4')
      | r1_tsep_1('#skF_2',C_167)
      | ~ m1_pre_topc(C_167,'#skF_1')
      | v2_struct_0(C_167) ) ),
    inference(resolution,[status(thm)],[c_953,c_16])).

tff(c_1330,plain,(
    ! [C_181,A_182] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_181),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_181),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2',C_181),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2',C_181))
      | ~ m1_pre_topc(C_181,'#skF_4')
      | r1_tsep_1('#skF_2',C_181)
      | ~ m1_pre_topc(C_181,'#skF_1')
      | v2_struct_0(C_181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_963])).

tff(c_1333,plain,(
    ! [A_182] :
      ( ~ m1_pre_topc('#skF_3',A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_1330])).

tff(c_1336,plain,(
    ! [A_182] :
      ( ~ m1_pre_topc('#skF_3',A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_62,c_1333])).

tff(c_1337,plain,(
    ! [A_182] :
      ( ~ m1_pre_topc('#skF_3',A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_34,c_1336])).

tff(c_1338,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1337])).

tff(c_1341,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_1338])).

tff(c_1344,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_1341])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_1344])).

tff(c_1348,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_1337])).

tff(c_1347,plain,(
    ! [A_182] :
      ( v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_3',A_182)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_182)
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(splitRight,[status(thm)],[c_1337])).

tff(c_1364,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1347])).

tff(c_1367,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1364,c_10])).

tff(c_1370,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_1367])).

tff(c_1372,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_1370])).

tff(c_1411,plain,(
    ! [A_187] :
      ( ~ m1_pre_topc('#skF_3',A_187)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_187)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(splitRight,[status(thm)],[c_1347])).

tff(c_1414,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1348,c_1411])).

tff(c_1437,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_1414])).

tff(c_1439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1437])).

tff(c_1440,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3')
    | m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1442,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1440])).

tff(c_4150,plain,(
    ! [A_426,B_427,C_428,D_429] :
      ( m1_pre_topc(k2_tsep_1(A_426,B_427,C_428),k2_tsep_1(A_426,D_429,C_428))
      | ~ m1_pre_topc(B_427,D_429)
      | r1_tsep_1(B_427,C_428)
      | ~ m1_pre_topc(D_429,A_426)
      | v2_struct_0(D_429)
      | ~ m1_pre_topc(C_428,A_426)
      | v2_struct_0(C_428)
      | ~ m1_pre_topc(B_427,A_426)
      | v2_struct_0(B_427)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2980,plain,(
    ! [A_336,B_337,C_338,D_339] :
      ( m1_pre_topc(k2_tsep_1(A_336,B_337,C_338),k2_tsep_1(A_336,B_337,D_339))
      | ~ m1_pre_topc(C_338,D_339)
      | r1_tsep_1(B_337,C_338)
      | ~ m1_pre_topc(D_339,A_336)
      | v2_struct_0(D_339)
      | ~ m1_pre_topc(C_338,A_336)
      | v2_struct_0(C_338)
      | ~ m1_pre_topc(B_337,A_336)
      | v2_struct_0(B_337)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1807,plain,(
    ! [A_243,B_244,C_245,D_246] :
      ( m1_pre_topc(k2_tsep_1(A_243,B_244,C_245),k2_tsep_1(A_243,D_246,C_245))
      | ~ m1_pre_topc(B_244,D_246)
      | r1_tsep_1(B_244,C_245)
      | ~ m1_pre_topc(D_246,A_243)
      | v2_struct_0(D_246)
      | ~ m1_pre_topc(C_245,A_243)
      | v2_struct_0(C_245)
      | ~ m1_pre_topc(B_244,A_243)
      | v2_struct_0(B_244)
      | ~ l1_pre_topc(A_243)
      | ~ v2_pre_topc(A_243)
      | v2_struct_0(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_1441,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_1457,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1441,c_54])).

tff(c_1458,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1457])).

tff(c_1524,plain,(
    ! [D_212,C_213,B_214,A_215] :
      ( ~ r1_tsep_1(D_212,C_213)
      | r1_tsep_1(D_212,B_214)
      | ~ m1_pre_topc(B_214,C_213)
      | ~ m1_pre_topc(D_212,A_215)
      | v2_struct_0(D_212)
      | ~ m1_pre_topc(C_213,A_215)
      | v2_struct_0(C_213)
      | ~ m1_pre_topc(B_214,A_215)
      | v2_struct_0(B_214)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1528,plain,(
    ! [B_214,A_215] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),B_214)
      | ~ m1_pre_topc(B_214,'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_215)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_215)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_214,A_215)
      | v2_struct_0(B_214)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_1458,c_1524])).

tff(c_1534,plain,(
    ! [B_214,A_215] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),B_214)
      | ~ m1_pre_topc(B_214,'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_215)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_215)
      | ~ m1_pre_topc(B_214,A_215)
      | v2_struct_0(B_214)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1528])).

tff(c_1536,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1534])).

tff(c_1539,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1536,c_10])).

tff(c_1542,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_44,c_1539])).

tff(c_1544,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_46,c_1542])).

tff(c_1546,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1534])).

tff(c_1676,plain,(
    ! [C_228,D_229,B_230,A_231] :
      ( ~ r1_tsep_1(C_228,D_229)
      | r1_tsep_1(B_230,D_229)
      | ~ m1_pre_topc(B_230,C_228)
      | ~ m1_pre_topc(D_229,A_231)
      | v2_struct_0(D_229)
      | ~ m1_pre_topc(C_228,A_231)
      | v2_struct_0(C_228)
      | ~ m1_pre_topc(B_230,A_231)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1684,plain,(
    ! [B_230,A_231] :
      ( r1_tsep_1(B_230,'#skF_3')
      | ~ m1_pre_topc(B_230,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_231)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_231)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc(B_230,A_231)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(resolution,[status(thm)],[c_1458,c_1676])).

tff(c_1696,plain,(
    ! [B_230,A_231] :
      ( r1_tsep_1(B_230,'#skF_3')
      | ~ m1_pre_topc(B_230,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_231)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_231)
      | ~ m1_pre_topc(B_230,A_231)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1546,c_42,c_1684])).

tff(c_1816,plain,(
    ! [B_244,A_231] :
      ( r1_tsep_1(k2_tsep_1('#skF_1',B_244,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_231)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_231)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_244,'#skF_2'),A_231)
      | v2_struct_0(k2_tsep_1('#skF_1',B_244,'#skF_2'))
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231)
      | ~ m1_pre_topc(B_244,'#skF_4')
      | r1_tsep_1(B_244,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_244,'#skF_1')
      | v2_struct_0(B_244)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1807,c_1696])).

tff(c_1839,plain,(
    ! [B_244,A_231] :
      ( r1_tsep_1(k2_tsep_1('#skF_1',B_244,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_231)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_231)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_244,'#skF_2'),A_231)
      | v2_struct_0(k2_tsep_1('#skF_1',B_244,'#skF_2'))
      | ~ l1_pre_topc(A_231)
      | ~ v2_pre_topc(A_231)
      | v2_struct_0(A_231)
      | ~ m1_pre_topc(B_244,'#skF_4')
      | r1_tsep_1(B_244,'#skF_2')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_244,'#skF_1')
      | v2_struct_0(B_244)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_36,c_1816])).

tff(c_1855,plain,(
    ! [B_247,A_248] :
      ( r1_tsep_1(k2_tsep_1('#skF_1',B_247,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_248)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_248)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_247,'#skF_2'),A_248)
      | v2_struct_0(k2_tsep_1('#skF_1',B_247,'#skF_2'))
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248)
      | ~ m1_pre_topc(B_247,'#skF_4')
      | r1_tsep_1(B_247,'#skF_2')
      | ~ m1_pre_topc(B_247,'#skF_1')
      | v2_struct_0(B_247) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_1839])).

tff(c_1867,plain,(
    ! [B_247] :
      ( r1_tsep_1(k2_tsep_1('#skF_1',B_247,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_247,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_247,'#skF_2'))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_247,'#skF_4')
      | r1_tsep_1(B_247,'#skF_2')
      | ~ m1_pre_topc(B_247,'#skF_1')
      | v2_struct_0(B_247)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_1855])).

tff(c_1882,plain,(
    ! [B_247] :
      ( r1_tsep_1(k2_tsep_1('#skF_1',B_247,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_247,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_247,'#skF_2'))
      | ~ m1_pre_topc(B_247,'#skF_4')
      | r1_tsep_1(B_247,'#skF_2')
      | ~ m1_pre_topc(B_247,'#skF_1')
      | v2_struct_0(B_247)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_44,c_50,c_40,c_1867])).

tff(c_1884,plain,(
    ! [B_249] :
      ( r1_tsep_1(k2_tsep_1('#skF_1',B_249,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_249,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_249,'#skF_2'))
      | ~ m1_pre_topc(B_249,'#skF_4')
      | r1_tsep_1(B_249,'#skF_2')
      | ~ m1_pre_topc(B_249,'#skF_1')
      | v2_struct_0(B_249) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_46,c_1882])).

tff(c_1894,plain,(
    ! [B_249,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_249,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_10)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_249,'#skF_2'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_249,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_249,'#skF_2'))
      | ~ m1_pre_topc(B_249,'#skF_4')
      | r1_tsep_1(B_249,'#skF_2')
      | ~ m1_pre_topc(B_249,'#skF_1')
      | v2_struct_0(B_249) ) ),
    inference(resolution,[status(thm)],[c_1884,c_16])).

tff(c_2536,plain,(
    ! [B_284,A_285] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_284,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_284,'#skF_2'),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_284,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_284,'#skF_2'))
      | ~ m1_pre_topc(B_284,'#skF_4')
      | r1_tsep_1(B_284,'#skF_2')
      | ~ m1_pre_topc(B_284,'#skF_1')
      | v2_struct_0(B_284) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1894])).

tff(c_2539,plain,(
    ! [A_285] :
      ( ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_2536])).

tff(c_2542,plain,(
    ! [A_285] :
      ( ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_44,c_62,c_2539])).

tff(c_2543,plain,(
    ! [A_285] :
      ( ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_2542])).

tff(c_2545,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2543])).

tff(c_2548,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_2545])).

tff(c_2551,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_2548])).

tff(c_2553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_2551])).

tff(c_2555,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_2543])).

tff(c_63,plain,(
    ! [B_66,A_67] :
      ( l1_pre_topc(B_66)
      | ~ m1_pre_topc(B_66,A_67)
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_79,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_69])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_82,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_72])).

tff(c_1451,plain,(
    ! [A_194,B_195,C_196] :
      ( m1_pre_topc(k2_tsep_1(A_194,B_195,C_196),A_194)
      | ~ m1_pre_topc(C_196,A_194)
      | v2_struct_0(C_196)
      | ~ m1_pre_topc(B_195,A_194)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1455,plain,(
    ! [A_194,B_195,C_196] :
      ( l1_pre_topc(k2_tsep_1(A_194,B_195,C_196))
      | ~ m1_pre_topc(C_196,A_194)
      | v2_struct_0(C_196)
      | ~ m1_pre_topc(B_195,A_194)
      | v2_struct_0(B_195)
      | ~ l1_pre_topc(A_194)
      | v2_struct_0(A_194) ) ),
    inference(resolution,[status(thm)],[c_1451,c_4])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tsep_1(B_9,A_8)
      | ~ r1_tsep_1(A_8,B_9)
      | ~ l1_struct_0(B_9)
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1461,plain,
    ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1','#skF_4','#skF_2'))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1458,c_12])).

tff(c_1462,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1461])).

tff(c_1466,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_1462])).

tff(c_1469,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1455,c_1466])).

tff(c_1472,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_44,c_1469])).

tff(c_1474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_46,c_1472])).

tff(c_1475,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3',k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1461])).

tff(c_1483,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1475])).

tff(c_1486,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_1483])).

tff(c_1490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1486])).

tff(c_1492,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1475])).

tff(c_2554,plain,(
    ! [A_285] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(splitRight,[status(thm)],[c_2543])).

tff(c_2570,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2554])).

tff(c_2573,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2570,c_10])).

tff(c_2576,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_2573])).

tff(c_2578,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_2576])).

tff(c_2579,plain,(
    ! [A_285] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_3',A_285)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_285)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(splitRight,[status(thm)],[c_2554])).

tff(c_2581,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2579])).

tff(c_2597,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2581,c_12])).

tff(c_2616,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1492,c_2597])).

tff(c_2617,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_2616])).

tff(c_2620,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_2617])).

tff(c_2624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2620])).

tff(c_2627,plain,(
    ! [A_290] :
      ( ~ m1_pre_topc('#skF_3',A_290)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_290)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290)
      | v2_struct_0(A_290) ) ),
    inference(splitRight,[status(thm)],[c_2579])).

tff(c_2630,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2555,c_2627])).

tff(c_2653,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_2630])).

tff(c_2655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2653])).

tff(c_2656,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1457])).

tff(c_2658,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2656])).

tff(c_2754,plain,(
    ! [D_314,C_315,B_316,A_317] :
      ( ~ r1_tsep_1(D_314,C_315)
      | r1_tsep_1(B_316,D_314)
      | ~ m1_pre_topc(B_316,C_315)
      | ~ m1_pre_topc(D_314,A_317)
      | v2_struct_0(D_314)
      | ~ m1_pre_topc(C_315,A_317)
      | v2_struct_0(C_315)
      | ~ m1_pre_topc(B_316,A_317)
      | v2_struct_0(B_316)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2758,plain,(
    ! [B_316,A_317] :
      ( r1_tsep_1(B_316,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_316,'#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_317)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_317)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_316,A_317)
      | v2_struct_0(B_316)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(resolution,[status(thm)],[c_2658,c_2754])).

tff(c_2764,plain,(
    ! [B_316,A_317] :
      ( r1_tsep_1(B_316,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_316,'#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_317)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_317)
      | ~ m1_pre_topc(B_316,A_317)
      | v2_struct_0(B_316)
      | ~ l1_pre_topc(A_317)
      | ~ v2_pre_topc(A_317)
      | v2_struct_0(A_317) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2758])).

tff(c_2776,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2764])).

tff(c_2779,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2776,c_10])).

tff(c_2782,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_2779])).

tff(c_2784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_2782])).

tff(c_2786,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2764])).

tff(c_2765,plain,(
    ! [C_318,D_319,B_320,A_321] :
      ( ~ r1_tsep_1(C_318,D_319)
      | r1_tsep_1(D_319,B_320)
      | ~ m1_pre_topc(B_320,C_318)
      | ~ m1_pre_topc(D_319,A_321)
      | v2_struct_0(D_319)
      | ~ m1_pre_topc(C_318,A_321)
      | v2_struct_0(C_318)
      | ~ m1_pre_topc(B_320,A_321)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2769,plain,(
    ! [B_320,A_321] :
      ( r1_tsep_1('#skF_2',B_320)
      | ~ m1_pre_topc(B_320,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_321)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_321)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_320,A_321)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(resolution,[status(thm)],[c_2658,c_2765])).

tff(c_2775,plain,(
    ! [B_320,A_321] :
      ( r1_tsep_1('#skF_2',B_320)
      | ~ m1_pre_topc(B_320,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_321)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_321)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_320,A_321)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2769])).

tff(c_2787,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2775])).

tff(c_2788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2786,c_2787])).

tff(c_2789,plain,(
    ! [B_320,A_321] :
      ( r1_tsep_1('#skF_2',B_320)
      | ~ m1_pre_topc(B_320,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_321)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_321)
      | ~ m1_pre_topc(B_320,A_321)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(splitRight,[status(thm)],[c_2775])).

tff(c_2989,plain,(
    ! [C_338,A_321] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_338))
      | ~ m1_pre_topc('#skF_2',A_321)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_321)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_338),A_321)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_338))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321)
      | ~ m1_pre_topc(C_338,'#skF_4')
      | r1_tsep_1('#skF_3',C_338)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_338,'#skF_1')
      | v2_struct_0(C_338)
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2980,c_2789])).

tff(c_3006,plain,(
    ! [C_338,A_321] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_338))
      | ~ m1_pre_topc('#skF_2',A_321)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_321)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_338),A_321)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_338))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321)
      | ~ m1_pre_topc(C_338,'#skF_4')
      | r1_tsep_1('#skF_3',C_338)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_338,'#skF_1')
      | v2_struct_0(C_338)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_36,c_2989])).

tff(c_3561,plain,(
    ! [C_368,A_369] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_368))
      | ~ m1_pre_topc('#skF_2',A_369)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_369)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_368),A_369)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_368))
      | ~ l1_pre_topc(A_369)
      | ~ v2_pre_topc(A_369)
      | v2_struct_0(A_369)
      | ~ m1_pre_topc(C_368,'#skF_4')
      | r1_tsep_1('#skF_3',C_368)
      | ~ m1_pre_topc(C_368,'#skF_1')
      | v2_struct_0(C_368) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_3006])).

tff(c_3576,plain,(
    ! [C_368] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_368))
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_368),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_368))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_368,'#skF_4')
      | r1_tsep_1('#skF_3',C_368)
      | ~ m1_pre_topc(C_368,'#skF_1')
      | v2_struct_0(C_368)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_3561])).

tff(c_3595,plain,(
    ! [C_368] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_368))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_368),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_368))
      | ~ m1_pre_topc(C_368,'#skF_4')
      | r1_tsep_1('#skF_3',C_368)
      | ~ m1_pre_topc(C_368,'#skF_1')
      | v2_struct_0(C_368)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_50,c_44,c_3576])).

tff(c_3597,plain,(
    ! [C_370] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_370))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_370),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_370))
      | ~ m1_pre_topc(C_370,'#skF_4')
      | r1_tsep_1('#skF_3',C_370)
      | ~ m1_pre_topc(C_370,'#skF_1')
      | v2_struct_0(C_370) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_3595])).

tff(c_14,plain,(
    ! [C_16,B_14,A_10] :
      ( ~ r1_tsep_1(C_16,B_14)
      | ~ m1_pre_topc(B_14,C_16)
      | ~ m1_pre_topc(C_16,A_10)
      | v2_struct_0(C_16)
      | ~ m1_pre_topc(B_14,A_10)
      | v2_struct_0(B_14)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_3607,plain,(
    ! [C_370,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_370),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_10)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_370),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_370),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_370))
      | ~ m1_pre_topc(C_370,'#skF_4')
      | r1_tsep_1('#skF_3',C_370)
      | ~ m1_pre_topc(C_370,'#skF_1')
      | v2_struct_0(C_370) ) ),
    inference(resolution,[status(thm)],[c_3597,c_14])).

tff(c_3696,plain,(
    ! [C_374,A_375] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_374),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_374),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_374),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_374))
      | ~ m1_pre_topc(C_374,'#skF_4')
      | r1_tsep_1('#skF_3',C_374)
      | ~ m1_pre_topc(C_374,'#skF_1')
      | v2_struct_0(C_374) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3607])).

tff(c_3699,plain,(
    ! [A_375] :
      ( ~ m1_pre_topc('#skF_2',A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_2','#skF_4')
      | r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_3696])).

tff(c_3702,plain,(
    ! [A_375] :
      ( ~ m1_pre_topc('#skF_2',A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_44,c_1442,c_3699])).

tff(c_3703,plain,(
    ! [A_375] :
      ( ~ m1_pre_topc('#skF_2',A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_3702])).

tff(c_3704,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_3703])).

tff(c_3707,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_3704])).

tff(c_3710,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_3707])).

tff(c_3712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_3710])).

tff(c_3714,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_3703])).

tff(c_2661,plain,
    ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2658,c_12])).

tff(c_2662,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2661])).

tff(c_2672,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_2662])).

tff(c_2675,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1455,c_2672])).

tff(c_2678,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_2675])).

tff(c_2680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_2678])).

tff(c_2681,plain,
    ( ~ l1_struct_0('#skF_2')
    | r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2661])).

tff(c_2683,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2681])).

tff(c_2686,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_2683])).

tff(c_2690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2686])).

tff(c_2692,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2681])).

tff(c_3713,plain,(
    ! [A_375] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(splitRight,[status(thm)],[c_3703])).

tff(c_3730,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3713])).

tff(c_3775,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3730,c_10])).

tff(c_3778,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_3775])).

tff(c_3780,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_3778])).

tff(c_3781,plain,(
    ! [A_375] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_375)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(splitRight,[status(thm)],[c_3713])).

tff(c_3783,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3781])).

tff(c_3797,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_3783,c_12])).

tff(c_3816,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2692,c_3797])).

tff(c_3817,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3816])).

tff(c_3820,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_3817])).

tff(c_3824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3820])).

tff(c_3829,plain,(
    ! [A_382] :
      ( ~ m1_pre_topc('#skF_2',A_382)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_382)
      | ~ l1_pre_topc(A_382)
      | ~ v2_pre_topc(A_382)
      | v2_struct_0(A_382) ) ),
    inference(splitRight,[status(thm)],[c_3781])).

tff(c_3832,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3714,c_3829])).

tff(c_3855,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_3832])).

tff(c_3857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3855])).

tff(c_3858,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_3955,plain,(
    ! [C_406,D_407,B_408,A_409] :
      ( ~ r1_tsep_1(C_406,D_407)
      | r1_tsep_1(D_407,B_408)
      | ~ m1_pre_topc(B_408,C_406)
      | ~ m1_pre_topc(D_407,A_409)
      | v2_struct_0(D_407)
      | ~ m1_pre_topc(C_406,A_409)
      | v2_struct_0(C_406)
      | ~ m1_pre_topc(B_408,A_409)
      | v2_struct_0(B_408)
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3959,plain,(
    ! [B_408,A_409] :
      ( r1_tsep_1('#skF_2',B_408)
      | ~ m1_pre_topc(B_408,k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_409)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_409)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_408,A_409)
      | v2_struct_0(B_408)
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(resolution,[status(thm)],[c_3858,c_3955])).

tff(c_3965,plain,(
    ! [B_408,A_409] :
      ( r1_tsep_1('#skF_2',B_408)
      | ~ m1_pre_topc(B_408,k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_409)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_409)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_408,A_409)
      | v2_struct_0(B_408)
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3959])).

tff(c_3977,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3965])).

tff(c_3980,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3977,c_10])).

tff(c_3983,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_40,c_3980])).

tff(c_3985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_42,c_3983])).

tff(c_3986,plain,(
    ! [B_408,A_409] :
      ( r1_tsep_1('#skF_2',B_408)
      | ~ m1_pre_topc(B_408,k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_409)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_409)
      | ~ m1_pre_topc(B_408,A_409)
      | v2_struct_0(B_408)
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409) ) ),
    inference(splitRight,[status(thm)],[c_3965])).

tff(c_4159,plain,(
    ! [B_427,A_409] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_427,'#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_409)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_409)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_427,'#skF_3'),A_409)
      | v2_struct_0(k2_tsep_1('#skF_1',B_427,'#skF_3'))
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409)
      | ~ m1_pre_topc(B_427,'#skF_4')
      | r1_tsep_1(B_427,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_427,'#skF_1')
      | v2_struct_0(B_427)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4150,c_3986])).

tff(c_4173,plain,(
    ! [B_427,A_409] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_427,'#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_409)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_409)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_427,'#skF_3'),A_409)
      | v2_struct_0(k2_tsep_1('#skF_1',B_427,'#skF_3'))
      | ~ l1_pre_topc(A_409)
      | ~ v2_pre_topc(A_409)
      | v2_struct_0(A_409)
      | ~ m1_pre_topc(B_427,'#skF_4')
      | r1_tsep_1(B_427,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_427,'#skF_1')
      | v2_struct_0(B_427)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_36,c_4159])).

tff(c_4759,plain,(
    ! [B_460,A_461] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_460,'#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_461)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_461)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_460,'#skF_3'),A_461)
      | v2_struct_0(k2_tsep_1('#skF_1',B_460,'#skF_3'))
      | ~ l1_pre_topc(A_461)
      | ~ v2_pre_topc(A_461)
      | v2_struct_0(A_461)
      | ~ m1_pre_topc(B_460,'#skF_4')
      | r1_tsep_1(B_460,'#skF_3')
      | ~ m1_pre_topc(B_460,'#skF_1')
      | v2_struct_0(B_460) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_4173])).

tff(c_4774,plain,(
    ! [B_460] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_460,'#skF_3'))
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_460,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_460,'#skF_3'))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_460,'#skF_4')
      | r1_tsep_1(B_460,'#skF_3')
      | ~ m1_pre_topc(B_460,'#skF_1')
      | v2_struct_0(B_460)
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_4759])).

tff(c_4793,plain,(
    ! [B_460] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_460,'#skF_3'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_460,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_460,'#skF_3'))
      | ~ m1_pre_topc(B_460,'#skF_4')
      | r1_tsep_1(B_460,'#skF_3')
      | ~ m1_pre_topc(B_460,'#skF_1')
      | v2_struct_0(B_460)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_40,c_50,c_44,c_4774])).

tff(c_4795,plain,(
    ! [B_462] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_462,'#skF_3'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_462,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_462,'#skF_3'))
      | ~ m1_pre_topc(B_462,'#skF_4')
      | r1_tsep_1(B_462,'#skF_3')
      | ~ m1_pre_topc(B_462,'#skF_1')
      | v2_struct_0(B_462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_42,c_4793])).

tff(c_4805,plain,(
    ! [B_462,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_462,'#skF_3'),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_10)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_462,'#skF_3'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_462,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_462,'#skF_3'))
      | ~ m1_pre_topc(B_462,'#skF_4')
      | r1_tsep_1(B_462,'#skF_3')
      | ~ m1_pre_topc(B_462,'#skF_1')
      | v2_struct_0(B_462) ) ),
    inference(resolution,[status(thm)],[c_4795,c_14])).

tff(c_5012,plain,(
    ! [B_476,A_477] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_476,'#skF_3'),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_476,'#skF_3'),A_477)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_476,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_476,'#skF_3'))
      | ~ m1_pre_topc(B_476,'#skF_4')
      | r1_tsep_1(B_476,'#skF_3')
      | ~ m1_pre_topc(B_476,'#skF_1')
      | v2_struct_0(B_476) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4805])).

tff(c_5015,plain,(
    ! [A_477] :
      ( ~ m1_pre_topc('#skF_2',A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_477)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_2','#skF_4')
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_5012])).

tff(c_5018,plain,(
    ! [A_477] :
      ( ~ m1_pre_topc('#skF_2',A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_477)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_1442,c_5015])).

tff(c_5019,plain,(
    ! [A_477] :
      ( ~ m1_pre_topc('#skF_2',A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_477)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_34,c_5018])).

tff(c_5022,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_5019])).

tff(c_5025,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_5022])).

tff(c_5028,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_5025])).

tff(c_5030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_5028])).

tff(c_5032,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5019])).

tff(c_5031,plain,(
    ! [A_477] :
      ( v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_477)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_477)
      | ~ l1_pre_topc(A_477)
      | ~ v2_pre_topc(A_477)
      | v2_struct_0(A_477) ) ),
    inference(splitRight,[status(thm)],[c_5019])).

tff(c_5047,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5031])).

tff(c_5050,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5047,c_10])).

tff(c_5053,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_5050])).

tff(c_5055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_5053])).

tff(c_5058,plain,(
    ! [A_480] :
      ( ~ m1_pre_topc('#skF_2',A_480)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_480)
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(splitRight,[status(thm)],[c_5031])).

tff(c_5061,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5032,c_5058])).

tff(c_5084,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_5061])).

tff(c_5086,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_5084])).

tff(c_5087,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1440])).

tff(c_5187,plain,(
    ! [D_521,C_522,B_523,A_524] :
      ( ~ r1_tsep_1(D_521,C_522)
      | r1_tsep_1(B_523,D_521)
      | ~ m1_pre_topc(B_523,C_522)
      | ~ m1_pre_topc(D_521,A_524)
      | v2_struct_0(D_521)
      | ~ m1_pre_topc(C_522,A_524)
      | v2_struct_0(C_522)
      | ~ m1_pre_topc(B_523,A_524)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5191,plain,(
    ! [B_523,A_524] :
      ( r1_tsep_1(B_523,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc(B_523,'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_524)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_524)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_523,A_524)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(resolution,[status(thm)],[c_5087,c_5187])).

tff(c_5197,plain,(
    ! [B_523,A_524] :
      ( r1_tsep_1(B_523,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc(B_523,'#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_524)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_524)
      | ~ m1_pre_topc(B_523,A_524)
      | v2_struct_0(B_523)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5191])).

tff(c_5220,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5197])).

tff(c_5223,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5220,c_10])).

tff(c_5226,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_44,c_5223])).

tff(c_5228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_46,c_5226])).

tff(c_5230,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5197])).

tff(c_5209,plain,(
    ! [C_529,D_530,B_531,A_532] :
      ( ~ r1_tsep_1(C_529,D_530)
      | r1_tsep_1(D_530,B_531)
      | ~ m1_pre_topc(B_531,C_529)
      | ~ m1_pre_topc(D_530,A_532)
      | v2_struct_0(D_530)
      | ~ m1_pre_topc(C_529,A_532)
      | v2_struct_0(C_529)
      | ~ m1_pre_topc(B_531,A_532)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5213,plain,(
    ! [B_531,A_532] :
      ( r1_tsep_1('#skF_3',B_531)
      | ~ m1_pre_topc(B_531,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_532)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_532)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc(B_531,A_532)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532) ) ),
    inference(resolution,[status(thm)],[c_5087,c_5209])).

tff(c_5219,plain,(
    ! [B_531,A_532] :
      ( r1_tsep_1('#skF_3',B_531)
      | ~ m1_pre_topc(B_531,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_532)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_532)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc(B_531,A_532)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_5213])).

tff(c_5529,plain,(
    ! [B_554,A_555] :
      ( r1_tsep_1('#skF_3',B_554)
      | ~ m1_pre_topc(B_554,k2_tsep_1('#skF_1','#skF_4','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_555)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_555)
      | ~ m1_pre_topc(B_554,A_555)
      | v2_struct_0(B_554)
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555) ) ),
    inference(negUnitSimplification,[status(thm)],[c_5230,c_5219])).

tff(c_5535,plain,(
    ! [B_47,A_555] :
      ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1',B_47,'#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_555)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_555)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_47,'#skF_2'),A_555)
      | v2_struct_0(k2_tsep_1('#skF_1',B_47,'#skF_2'))
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555)
      | ~ m1_pre_topc(B_47,'#skF_4')
      | r1_tsep_1(B_47,'#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_47,'#skF_1')
      | v2_struct_0(B_47)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_5529])).

tff(c_5551,plain,(
    ! [B_47,A_555] :
      ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1',B_47,'#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_555)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_555)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_47,'#skF_2'),A_555)
      | v2_struct_0(k2_tsep_1('#skF_1',B_47,'#skF_2'))
      | ~ l1_pre_topc(A_555)
      | ~ v2_pre_topc(A_555)
      | v2_struct_0(A_555)
      | ~ m1_pre_topc(B_47,'#skF_4')
      | r1_tsep_1(B_47,'#skF_2')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_47,'#skF_1')
      | v2_struct_0(B_47)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_36,c_5535])).

tff(c_5990,plain,(
    ! [B_579,A_580] :
      ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1',B_579,'#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_580)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2'),A_580)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_579,'#skF_2'),A_580)
      | v2_struct_0(k2_tsep_1('#skF_1',B_579,'#skF_2'))
      | ~ l1_pre_topc(A_580)
      | ~ v2_pre_topc(A_580)
      | v2_struct_0(A_580)
      | ~ m1_pre_topc(B_579,'#skF_4')
      | r1_tsep_1(B_579,'#skF_2')
      | ~ m1_pre_topc(B_579,'#skF_1')
      | v2_struct_0(B_579) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_38,c_5551])).

tff(c_6005,plain,(
    ! [B_579] :
      ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1',B_579,'#skF_2'))
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_579,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_579,'#skF_2'))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_579,'#skF_4')
      | r1_tsep_1(B_579,'#skF_2')
      | ~ m1_pre_topc(B_579,'#skF_1')
      | v2_struct_0(B_579)
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_5990])).

tff(c_6024,plain,(
    ! [B_579] :
      ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1',B_579,'#skF_2'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_579,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_579,'#skF_2'))
      | ~ m1_pre_topc(B_579,'#skF_4')
      | r1_tsep_1(B_579,'#skF_2')
      | ~ m1_pre_topc(B_579,'#skF_1')
      | v2_struct_0(B_579)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_44,c_50,c_40,c_6005])).

tff(c_6026,plain,(
    ! [B_581] :
      ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1',B_581,'#skF_2'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_581,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_581,'#skF_2'))
      | ~ m1_pre_topc(B_581,'#skF_4')
      | r1_tsep_1(B_581,'#skF_2')
      | ~ m1_pre_topc(B_581,'#skF_1')
      | v2_struct_0(B_581) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_46,c_6024])).

tff(c_6036,plain,(
    ! [B_581,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_581,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_10)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_581,'#skF_2'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_581,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_581,'#skF_2'))
      | ~ m1_pre_topc(B_581,'#skF_4')
      | r1_tsep_1(B_581,'#skF_2')
      | ~ m1_pre_topc(B_581,'#skF_1')
      | v2_struct_0(B_581) ) ),
    inference(resolution,[status(thm)],[c_6026,c_14])).

tff(c_6321,plain,(
    ! [B_597,A_598] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_597,'#skF_2'),'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_597,'#skF_2'),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_597,'#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_597,'#skF_2'))
      | ~ m1_pre_topc(B_597,'#skF_4')
      | r1_tsep_1(B_597,'#skF_2')
      | ~ m1_pre_topc(B_597,'#skF_1')
      | v2_struct_0(B_597) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_6036])).

tff(c_6324,plain,(
    ! [A_598] :
      ( ~ m1_pre_topc('#skF_3',A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_6321])).

tff(c_6327,plain,(
    ! [A_598] :
      ( ~ m1_pre_topc('#skF_3',A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_44,c_62,c_6324])).

tff(c_6328,plain,(
    ! [A_598] :
      ( ~ m1_pre_topc('#skF_3',A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_6327])).

tff(c_6329,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6328])).

tff(c_6332,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_6329])).

tff(c_6335,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_6332])).

tff(c_6337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_6335])).

tff(c_6339,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_6328])).

tff(c_5101,plain,(
    ! [A_487,B_488,C_489] :
      ( m1_pre_topc(k2_tsep_1(A_487,B_488,C_489),A_487)
      | ~ m1_pre_topc(C_489,A_487)
      | v2_struct_0(C_489)
      | ~ m1_pre_topc(B_488,A_487)
      | v2_struct_0(B_488)
      | ~ l1_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5106,plain,(
    ! [A_490,B_491,C_492] :
      ( l1_pre_topc(k2_tsep_1(A_490,B_491,C_492))
      | ~ m1_pre_topc(C_492,A_490)
      | v2_struct_0(C_492)
      | ~ m1_pre_topc(B_491,A_490)
      | v2_struct_0(B_491)
      | ~ l1_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_5101,c_4])).

tff(c_5091,plain,
    ( r1_tsep_1('#skF_3',k2_tsep_1('#skF_1','#skF_4','#skF_2'))
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5087,c_12])).

tff(c_5092,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5091])).

tff(c_5096,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_5092])).

tff(c_5109,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_5106,c_5096])).

tff(c_5112,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_44,c_5109])).

tff(c_5114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_46,c_5112])).

tff(c_5115,plain,
    ( ~ l1_struct_0('#skF_3')
    | r1_tsep_1('#skF_3',k2_tsep_1('#skF_1','#skF_4','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_5091])).

tff(c_5118,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5115])).

tff(c_5121,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_5118])).

tff(c_5125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5121])).

tff(c_5127,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_5115])).

tff(c_6338,plain,(
    ! [A_598] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(splitRight,[status(thm)],[c_6328])).

tff(c_6356,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6338])).

tff(c_6359,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6356,c_10])).

tff(c_6362,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_6359])).

tff(c_6364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_6362])).

tff(c_6365,plain,(
    ! [A_598] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_3',A_598)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(splitRight,[status(thm)],[c_6338])).

tff(c_6367,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6365])).

tff(c_6381,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_6367,c_12])).

tff(c_6400,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5127,c_6381])).

tff(c_6401,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_6400])).

tff(c_6404,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_6401])).

tff(c_6408,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_6404])).

tff(c_6413,plain,(
    ! [A_603] :
      ( ~ m1_pre_topc('#skF_3',A_603)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_603)
      | ~ l1_pre_topc(A_603)
      | ~ v2_pre_topc(A_603)
      | v2_struct_0(A_603) ) ),
    inference(splitRight,[status(thm)],[c_6365])).

tff(c_6416,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6339,c_6413])).

tff(c_6439,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_6416])).

tff(c_6441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_6439])).

tff(c_6442,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6844,plain,(
    ! [A_678,B_679,C_680,D_681] :
      ( m1_pre_topc(k2_tsep_1(A_678,B_679,C_680),k2_tsep_1(A_678,D_681,C_680))
      | ~ m1_pre_topc(B_679,D_681)
      | r1_tsep_1(B_679,C_680)
      | ~ m1_pre_topc(D_681,A_678)
      | v2_struct_0(D_681)
      | ~ m1_pre_topc(C_680,A_678)
      | v2_struct_0(C_680)
      | ~ m1_pre_topc(B_679,A_678)
      | v2_struct_0(B_679)
      | ~ l1_pre_topc(A_678)
      | ~ v2_pre_topc(A_678)
      | v2_struct_0(A_678) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_6443,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2')
    | m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_6471,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_6443,c_58])).

tff(c_6472,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6471])).

tff(c_6565,plain,(
    ! [D_647,C_648,B_649,A_650] :
      ( ~ r1_tsep_1(D_647,C_648)
      | r1_tsep_1(D_647,B_649)
      | ~ m1_pre_topc(B_649,C_648)
      | ~ m1_pre_topc(D_647,A_650)
      | v2_struct_0(D_647)
      | ~ m1_pre_topc(C_648,A_650)
      | v2_struct_0(C_648)
      | ~ m1_pre_topc(B_649,A_650)
      | v2_struct_0(B_649)
      | ~ l1_pre_topc(A_650)
      | ~ v2_pre_topc(A_650)
      | v2_struct_0(A_650) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6569,plain,(
    ! [B_649,A_650] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),B_649)
      | ~ m1_pre_topc(B_649,'#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_650)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_650)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_649,A_650)
      | v2_struct_0(B_649)
      | ~ l1_pre_topc(A_650)
      | ~ v2_pre_topc(A_650)
      | v2_struct_0(A_650) ) ),
    inference(resolution,[status(thm)],[c_6472,c_6565])).

tff(c_6575,plain,(
    ! [B_649,A_650] :
      ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_4','#skF_3'),B_649)
      | ~ m1_pre_topc(B_649,'#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_650)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_650)
      | ~ m1_pre_topc(B_649,A_650)
      | v2_struct_0(B_649)
      | ~ l1_pre_topc(A_650)
      | ~ v2_pre_topc(A_650)
      | v2_struct_0(A_650) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_6569])).

tff(c_6576,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6575])).

tff(c_6579,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6576,c_10])).

tff(c_6582,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_40,c_6579])).

tff(c_6584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_42,c_6582])).

tff(c_6586,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6575])).

tff(c_6804,plain,(
    ! [C_672,D_673,B_674,A_675] :
      ( ~ r1_tsep_1(C_672,D_673)
      | r1_tsep_1(D_673,B_674)
      | ~ m1_pre_topc(B_674,C_672)
      | ~ m1_pre_topc(D_673,A_675)
      | v2_struct_0(D_673)
      | ~ m1_pre_topc(C_672,A_675)
      | v2_struct_0(C_672)
      | ~ m1_pre_topc(B_674,A_675)
      | v2_struct_0(B_674)
      | ~ l1_pre_topc(A_675)
      | ~ v2_pre_topc(A_675)
      | v2_struct_0(A_675) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_6812,plain,(
    ! [B_674,A_675] :
      ( r1_tsep_1('#skF_2',B_674)
      | ~ m1_pre_topc(B_674,k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_675)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_675)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc(B_674,A_675)
      | v2_struct_0(B_674)
      | ~ l1_pre_topc(A_675)
      | ~ v2_pre_topc(A_675)
      | v2_struct_0(A_675) ) ),
    inference(resolution,[status(thm)],[c_6472,c_6804])).

tff(c_6823,plain,(
    ! [B_674,A_675] :
      ( r1_tsep_1('#skF_2',B_674)
      | ~ m1_pre_topc(B_674,k2_tsep_1('#skF_1','#skF_4','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_675)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_675)
      | ~ m1_pre_topc(B_674,A_675)
      | v2_struct_0(B_674)
      | ~ l1_pre_topc(A_675)
      | ~ v2_pre_topc(A_675)
      | v2_struct_0(A_675) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6586,c_46,c_6812])).

tff(c_6847,plain,(
    ! [B_679,A_675] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_679,'#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_675)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_675)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_679,'#skF_3'),A_675)
      | v2_struct_0(k2_tsep_1('#skF_1',B_679,'#skF_3'))
      | ~ l1_pre_topc(A_675)
      | ~ v2_pre_topc(A_675)
      | v2_struct_0(A_675)
      | ~ m1_pre_topc(B_679,'#skF_4')
      | r1_tsep_1(B_679,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_679,'#skF_1')
      | v2_struct_0(B_679)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6844,c_6823])).

tff(c_6868,plain,(
    ! [B_679,A_675] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_679,'#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_675)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_675)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_679,'#skF_3'),A_675)
      | v2_struct_0(k2_tsep_1('#skF_1',B_679,'#skF_3'))
      | ~ l1_pre_topc(A_675)
      | ~ v2_pre_topc(A_675)
      | v2_struct_0(A_675)
      | ~ m1_pre_topc(B_679,'#skF_4')
      | r1_tsep_1(B_679,'#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_679,'#skF_1')
      | v2_struct_0(B_679)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_36,c_6847])).

tff(c_7039,plain,(
    ! [B_695,A_696] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_695,'#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_696)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_4','#skF_3'),A_696)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_695,'#skF_3'),A_696)
      | v2_struct_0(k2_tsep_1('#skF_1',B_695,'#skF_3'))
      | ~ l1_pre_topc(A_696)
      | ~ v2_pre_topc(A_696)
      | v2_struct_0(A_696)
      | ~ m1_pre_topc(B_695,'#skF_4')
      | r1_tsep_1(B_695,'#skF_3')
      | ~ m1_pre_topc(B_695,'#skF_1')
      | v2_struct_0(B_695) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_6868])).

tff(c_7054,plain,(
    ! [B_695] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_695,'#skF_3'))
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_695,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_695,'#skF_3'))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(B_695,'#skF_4')
      | r1_tsep_1(B_695,'#skF_3')
      | ~ m1_pre_topc(B_695,'#skF_1')
      | v2_struct_0(B_695)
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_7039])).

tff(c_7073,plain,(
    ! [B_695] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_695,'#skF_3'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_695,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_695,'#skF_3'))
      | ~ m1_pre_topc(B_695,'#skF_4')
      | r1_tsep_1(B_695,'#skF_3')
      | ~ m1_pre_topc(B_695,'#skF_1')
      | v2_struct_0(B_695)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_36,c_40,c_50,c_44,c_7054])).

tff(c_7075,plain,(
    ! [B_697] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1',B_697,'#skF_3'))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_697,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_697,'#skF_3'))
      | ~ m1_pre_topc(B_697,'#skF_4')
      | r1_tsep_1(B_697,'#skF_3')
      | ~ m1_pre_topc(B_697,'#skF_1')
      | v2_struct_0(B_697) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_38,c_42,c_7073])).

tff(c_7087,plain,(
    ! [B_697,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_697,'#skF_3'),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_10)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_697,'#skF_3'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_697,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_697,'#skF_3'))
      | ~ m1_pre_topc(B_697,'#skF_4')
      | r1_tsep_1(B_697,'#skF_3')
      | ~ m1_pre_topc(B_697,'#skF_1')
      | v2_struct_0(B_697) ) ),
    inference(resolution,[status(thm)],[c_7075,c_14])).

tff(c_7810,plain,(
    ! [B_734,A_735] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1',B_734,'#skF_3'),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_734,'#skF_3'),A_735)
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1',B_734,'#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1',B_734,'#skF_3'))
      | ~ m1_pre_topc(B_734,'#skF_4')
      | r1_tsep_1(B_734,'#skF_3')
      | ~ m1_pre_topc(B_734,'#skF_1')
      | v2_struct_0(B_734) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_7087])).

tff(c_7813,plain,(
    ! [A_735] :
      ( ~ m1_pre_topc('#skF_2',A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_735)
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_2','#skF_4')
      | r1_tsep_1('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_7810])).

tff(c_7816,plain,(
    ! [A_735] :
      ( ~ m1_pre_topc('#skF_2',A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_735)
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | r1_tsep_1('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_6442,c_7813])).

tff(c_7817,plain,(
    ! [A_735] :
      ( ~ m1_pre_topc('#skF_2',A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_735)
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_34,c_7816])).

tff(c_7820,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_7817])).

tff(c_7823,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_7820])).

tff(c_7826,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_7823])).

tff(c_7828,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_7826])).

tff(c_7830,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_7817])).

tff(c_7829,plain,(
    ! [A_735] :
      ( v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
      | ~ m1_pre_topc('#skF_2',A_735)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_735)
      | ~ l1_pre_topc(A_735)
      | ~ v2_pre_topc(A_735)
      | v2_struct_0(A_735) ) ),
    inference(splitRight,[status(thm)],[c_7817])).

tff(c_7845,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7829])).

tff(c_7848,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7845,c_10])).

tff(c_7851,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_7848])).

tff(c_7853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_7851])).

tff(c_7856,plain,(
    ! [A_738] :
      ( ~ m1_pre_topc('#skF_2',A_738)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),A_738)
      | ~ l1_pre_topc(A_738)
      | ~ v2_pre_topc(A_738)
      | v2_struct_0(A_738) ) ),
    inference(splitRight,[status(thm)],[c_7829])).

tff(c_7859,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7830,c_7856])).

tff(c_7882,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_7859])).

tff(c_7884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7882])).

tff(c_7885,plain,(
    r1_tsep_1(k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_6471])).

tff(c_7985,plain,(
    ! [D_779,C_780,B_781,A_782] :
      ( ~ r1_tsep_1(D_779,C_780)
      | r1_tsep_1(B_781,D_779)
      | ~ m1_pre_topc(B_781,C_780)
      | ~ m1_pre_topc(D_779,A_782)
      | v2_struct_0(D_779)
      | ~ m1_pre_topc(C_780,A_782)
      | v2_struct_0(C_780)
      | ~ m1_pre_topc(B_781,A_782)
      | v2_struct_0(B_781)
      | ~ l1_pre_topc(A_782)
      | ~ v2_pre_topc(A_782)
      | v2_struct_0(A_782) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7989,plain,(
    ! [B_781,A_782] :
      ( r1_tsep_1(B_781,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_781,'#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_782)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_782)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_781,A_782)
      | v2_struct_0(B_781)
      | ~ l1_pre_topc(A_782)
      | ~ v2_pre_topc(A_782)
      | v2_struct_0(A_782) ) ),
    inference(resolution,[status(thm)],[c_7885,c_7985])).

tff(c_7995,plain,(
    ! [B_781,A_782] :
      ( r1_tsep_1(B_781,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_781,'#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_782)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_782)
      | ~ m1_pre_topc(B_781,A_782)
      | v2_struct_0(B_781)
      | ~ l1_pre_topc(A_782)
      | ~ v2_pre_topc(A_782)
      | v2_struct_0(A_782) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_7989])).

tff(c_8018,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7995])).

tff(c_8021,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8018,c_10])).

tff(c_8024,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_8021])).

tff(c_8026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_8024])).

tff(c_8028,plain,(
    ~ v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7995])).

tff(c_8007,plain,(
    ! [C_787,D_788,B_789,A_790] :
      ( ~ r1_tsep_1(C_787,D_788)
      | r1_tsep_1(D_788,B_789)
      | ~ m1_pre_topc(B_789,C_787)
      | ~ m1_pre_topc(D_788,A_790)
      | v2_struct_0(D_788)
      | ~ m1_pre_topc(C_787,A_790)
      | v2_struct_0(C_787)
      | ~ m1_pre_topc(B_789,A_790)
      | v2_struct_0(B_789)
      | ~ l1_pre_topc(A_790)
      | ~ v2_pre_topc(A_790)
      | v2_struct_0(A_790) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_8011,plain,(
    ! [B_789,A_790] :
      ( r1_tsep_1('#skF_2',B_789)
      | ~ m1_pre_topc(B_789,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_790)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_790)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_789,A_790)
      | v2_struct_0(B_789)
      | ~ l1_pre_topc(A_790)
      | ~ v2_pre_topc(A_790)
      | v2_struct_0(A_790) ) ),
    inference(resolution,[status(thm)],[c_7885,c_8007])).

tff(c_8017,plain,(
    ! [B_789,A_790] :
      ( r1_tsep_1('#skF_2',B_789)
      | ~ m1_pre_topc(B_789,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_790)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_790)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc(B_789,A_790)
      | v2_struct_0(B_789)
      | ~ l1_pre_topc(A_790)
      | ~ v2_pre_topc(A_790)
      | v2_struct_0(A_790) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_8011])).

tff(c_8327,plain,(
    ! [B_812,A_813] :
      ( r1_tsep_1('#skF_2',B_812)
      | ~ m1_pre_topc(B_812,k2_tsep_1('#skF_1','#skF_3','#skF_4'))
      | ~ m1_pre_topc('#skF_2',A_813)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_813)
      | ~ m1_pre_topc(B_812,A_813)
      | v2_struct_0(B_812)
      | ~ l1_pre_topc(A_813)
      | ~ v2_pre_topc(A_813)
      | v2_struct_0(A_813) ) ),
    inference(negUnitSimplification,[status(thm)],[c_8028,c_8017])).

tff(c_8330,plain,(
    ! [C_51,A_813] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_51))
      | ~ m1_pre_topc('#skF_2',A_813)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_813)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_51),A_813)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_51))
      | ~ l1_pre_topc(A_813)
      | ~ v2_pre_topc(A_813)
      | v2_struct_0(A_813)
      | ~ m1_pre_topc(C_51,'#skF_4')
      | r1_tsep_1('#skF_3',C_51)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_51,'#skF_1')
      | v2_struct_0(C_51)
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_8327])).

tff(c_8345,plain,(
    ! [C_51,A_813] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_51))
      | ~ m1_pre_topc('#skF_2',A_813)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_813)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_51),A_813)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_51))
      | ~ l1_pre_topc(A_813)
      | ~ v2_pre_topc(A_813)
      | v2_struct_0(A_813)
      | ~ m1_pre_topc(C_51,'#skF_4')
      | r1_tsep_1('#skF_3',C_51)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_51,'#skF_1')
      | v2_struct_0(C_51)
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_36,c_8330])).

tff(c_8540,plain,(
    ! [C_824,A_825] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_824))
      | ~ m1_pre_topc('#skF_2',A_825)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4'),A_825)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_824),A_825)
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_824))
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825)
      | v2_struct_0(A_825)
      | ~ m1_pre_topc(C_824,'#skF_4')
      | r1_tsep_1('#skF_3',C_824)
      | ~ m1_pre_topc(C_824,'#skF_1')
      | v2_struct_0(C_824) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_8345])).

tff(c_8555,plain,(
    ! [C_824] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_824))
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_824),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_824))
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_824,'#skF_4')
      | r1_tsep_1('#skF_3',C_824)
      | ~ m1_pre_topc(C_824,'#skF_1')
      | v2_struct_0(C_824)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_6,c_8540])).

tff(c_8574,plain,(
    ! [C_824] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_824))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_824),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_824))
      | ~ m1_pre_topc(C_824,'#skF_4')
      | r1_tsep_1('#skF_3',C_824)
      | ~ m1_pre_topc(C_824,'#skF_1')
      | v2_struct_0(C_824)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_50,c_44,c_8555])).

tff(c_8576,plain,(
    ! [C_826] :
      ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3',C_826))
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_826),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_826))
      | ~ m1_pre_topc(C_826,'#skF_4')
      | r1_tsep_1('#skF_3',C_826)
      | ~ m1_pre_topc(C_826,'#skF_1')
      | v2_struct_0(C_826) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_8574])).

tff(c_8586,plain,(
    ! [C_826,A_10] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_826),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_10)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_826),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_826),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_826))
      | ~ m1_pre_topc(C_826,'#skF_4')
      | r1_tsep_1('#skF_3',C_826)
      | ~ m1_pre_topc(C_826,'#skF_1')
      | v2_struct_0(C_826) ) ),
    inference(resolution,[status(thm)],[c_8576,c_14])).

tff(c_9186,plain,(
    ! [C_856,A_857] :
      ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_856),'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_856),A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3',C_856),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3',C_856))
      | ~ m1_pre_topc(C_856,'#skF_4')
      | r1_tsep_1('#skF_3',C_856)
      | ~ m1_pre_topc(C_856,'#skF_1')
      | v2_struct_0(C_856) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_8586])).

tff(c_9189,plain,(
    ! [A_857] :
      ( ~ m1_pre_topc('#skF_2',A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_2','#skF_4')
      | r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2','#skF_1')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_9186])).

tff(c_9192,plain,(
    ! [A_857] :
      ( ~ m1_pre_topc('#skF_2',A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_44,c_6442,c_9189])).

tff(c_9193,plain,(
    ! [A_857] :
      ( ~ m1_pre_topc('#skF_2',A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | r1_tsep_1('#skF_3','#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_9192])).

tff(c_9194,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_9193])).

tff(c_9197,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_9194])).

tff(c_9200,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_9197])).

tff(c_9202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_9200])).

tff(c_9204,plain,(
    m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_9193])).

tff(c_6445,plain,(
    ! [B_604,A_605] :
      ( l1_pre_topc(B_604)
      | ~ m1_pre_topc(B_604,A_605)
      | ~ l1_pre_topc(A_605) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_6454,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_6445])).

tff(c_6464,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6454])).

tff(c_6451,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_6445])).

tff(c_6461,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6451])).

tff(c_7899,plain,(
    ! [A_745,B_746,C_747] :
      ( m1_pre_topc(k2_tsep_1(A_745,B_746,C_747),A_745)
      | ~ m1_pre_topc(C_747,A_745)
      | v2_struct_0(C_747)
      | ~ m1_pre_topc(B_746,A_745)
      | v2_struct_0(B_746)
      | ~ l1_pre_topc(A_745)
      | v2_struct_0(A_745) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7904,plain,(
    ! [A_748,B_749,C_750] :
      ( l1_pre_topc(k2_tsep_1(A_748,B_749,C_750))
      | ~ m1_pre_topc(C_750,A_748)
      | v2_struct_0(C_750)
      | ~ m1_pre_topc(B_749,A_748)
      | v2_struct_0(B_749)
      | ~ l1_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(resolution,[status(thm)],[c_7899,c_4])).

tff(c_7889,plain,
    ( r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3','#skF_4'))
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7885,c_12])).

tff(c_7890,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7889])).

tff(c_7894,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_2,c_7890])).

tff(c_7907,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_7904,c_7894])).

tff(c_7910,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_36,c_7907])).

tff(c_7912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_38,c_7910])).

tff(c_7913,plain,
    ( ~ l1_struct_0('#skF_2')
    | r1_tsep_1('#skF_2',k2_tsep_1('#skF_1','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7889])).

tff(c_7916,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_7913])).

tff(c_7919,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_7916])).

tff(c_7923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6461,c_7919])).

tff(c_7925,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7913])).

tff(c_9203,plain,(
    ! [A_857] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2'))
      | ~ m1_pre_topc('#skF_2',A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857) ) ),
    inference(splitRight,[status(thm)],[c_9193])).

tff(c_9219,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9203])).

tff(c_9223,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_9219,c_10])).

tff(c_9226,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_44,c_9223])).

tff(c_9228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_46,c_9226])).

tff(c_9229,plain,(
    ! [A_857] :
      ( r1_tsep_1('#skF_3','#skF_2')
      | ~ m1_pre_topc('#skF_2',A_857)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_857)
      | ~ l1_pre_topc(A_857)
      | ~ v2_pre_topc(A_857)
      | v2_struct_0(A_857) ) ),
    inference(splitRight,[status(thm)],[c_9203])).

tff(c_9231,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_9229])).

tff(c_9245,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_9231,c_12])).

tff(c_9264,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7925,c_9245])).

tff(c_9265,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_9264])).

tff(c_9268,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_9265])).

tff(c_9272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6464,c_9268])).

tff(c_9275,plain,(
    ! [A_860] :
      ( ~ m1_pre_topc('#skF_2',A_860)
      | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_3','#skF_2'),A_860)
      | ~ l1_pre_topc(A_860)
      | ~ v2_pre_topc(A_860)
      | v2_struct_0(A_860) ) ),
    inference(splitRight,[status(thm)],[c_9229])).

tff(c_9278,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_9204,c_9275])).

tff(c_9301,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_9278])).

tff(c_9303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_9301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:41:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.46/3.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.62/3.81  
% 9.62/3.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.62/3.81  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.62/3.81  
% 9.62/3.81  %Foreground sorts:
% 9.62/3.81  
% 9.62/3.81  
% 9.62/3.81  %Background operators:
% 9.62/3.81  
% 9.62/3.81  
% 9.62/3.81  %Foreground operators:
% 9.62/3.81  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.62/3.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.62/3.81  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.62/3.81  tff('#skF_2', type, '#skF_2': $i).
% 9.62/3.81  tff('#skF_3', type, '#skF_3': $i).
% 9.62/3.81  tff('#skF_1', type, '#skF_1': $i).
% 9.62/3.81  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.62/3.81  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.62/3.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.62/3.81  tff('#skF_4', type, '#skF_4': $i).
% 9.62/3.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.62/3.81  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.62/3.81  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 9.62/3.81  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.62/3.81  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 9.62/3.81  
% 10.07/3.87  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((m1_pre_topc(B, D) => (~r1_tsep_1(k2_tsep_1(A, D, C), B) & ~r1_tsep_1(k2_tsep_1(A, C, D), B))) & (m1_pre_topc(C, D) => (~r1_tsep_1(k2_tsep_1(A, B, D), C) & ~r1_tsep_1(k2_tsep_1(A, D, B), C))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tmap_1)).
% 10.07/3.87  tff(f_58, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 10.07/3.87  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (m1_pre_topc(k2_tsep_1(A, B, C), B) & m1_pre_topc(k2_tsep_1(A, B, C), C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_tsep_1)).
% 10.07/3.87  tff(f_192, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((m1_pre_topc(B, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, D, C))) & (m1_pre_topc(C, D) => m1_pre_topc(k2_tsep_1(A, B, C), k2_tsep_1(A, B, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_tmap_1)).
% 10.07/3.87  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 10.07/3.87  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 10.07/3.87  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.07/3.87  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.07/3.87  tff(f_66, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 10.07/3.87  tff(c_52, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_44, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_46, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_pre_topc(k2_tsep_1(A_5, B_6, C_7), A_5) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~m1_pre_topc(B_6, A_5) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.07/3.87  tff(c_60, plain, (m1_pre_topc('#skF_2', '#skF_4') | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 10.07/3.87  tff(c_28, plain, (![A_32, B_36, C_38]: (m1_pre_topc(k2_tsep_1(A_32, B_36, C_38), B_36) | r1_tsep_1(B_36, C_38) | ~m1_pre_topc(C_38, A_32) | v2_struct_0(C_38) | ~m1_pre_topc(B_36, A_32) | v2_struct_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.07/3.87  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_32, plain, (![A_39, B_47, C_51, D_53]: (m1_pre_topc(k2_tsep_1(A_39, B_47, C_51), k2_tsep_1(A_39, D_53, C_51)) | ~m1_pre_topc(B_47, D_53) | r1_tsep_1(B_47, C_51) | ~m1_pre_topc(D_53, A_39) | v2_struct_0(D_53) | ~m1_pre_topc(C_51, A_39) | v2_struct_0(C_51) | ~m1_pre_topc(B_47, A_39) | v2_struct_0(B_47) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.07/3.87  tff(c_34, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_26, plain, (![A_32, B_36, C_38]: (m1_pre_topc(k2_tsep_1(A_32, B_36, C_38), C_38) | r1_tsep_1(B_36, C_38) | ~m1_pre_topc(C_38, A_32) | v2_struct_0(C_38) | ~m1_pre_topc(B_36, A_32) | v2_struct_0(B_36) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.07/3.87  tff(c_30, plain, (![A_39, B_47, C_51, D_53]: (m1_pre_topc(k2_tsep_1(A_39, B_47, C_51), k2_tsep_1(A_39, B_47, D_53)) | ~m1_pre_topc(C_51, D_53) | r1_tsep_1(B_47, C_51) | ~m1_pre_topc(D_53, A_39) | v2_struct_0(D_53) | ~m1_pre_topc(C_51, A_39) | v2_struct_0(C_51) | ~m1_pre_topc(B_47, A_39) | v2_struct_0(B_47) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.07/3.87  tff(c_56, plain, (m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_90, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_56])).
% 10.07/3.87  tff(c_197, plain, (![C_114, D_115, B_116, A_117]: (~r1_tsep_1(C_114, D_115) | r1_tsep_1(D_115, B_116) | ~m1_pre_topc(B_116, C_114) | ~m1_pre_topc(D_115, A_117) | v2_struct_0(D_115) | ~m1_pre_topc(C_114, A_117) | v2_struct_0(C_114) | ~m1_pre_topc(B_116, A_117) | v2_struct_0(B_116) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_201, plain, (![B_116, A_117]: (r1_tsep_1('#skF_3', B_116) | ~m1_pre_topc(B_116, k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_3', A_117) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_117) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc(B_116, A_117) | v2_struct_0(B_116) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(resolution, [status(thm)], [c_90, c_197])).
% 10.07/3.87  tff(c_207, plain, (![B_116, A_117]: (r1_tsep_1('#skF_3', B_116) | ~m1_pre_topc(B_116, k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_3', A_117) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_117) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc(B_116, A_117) | v2_struct_0(B_116) | ~l1_pre_topc(A_117) | ~v2_pre_topc(A_117) | v2_struct_0(A_117))), inference(negUnitSimplification, [status(thm)], [c_42, c_201])).
% 10.07/3.87  tff(c_219, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_207])).
% 10.07/3.87  tff(c_10, plain, (![A_5, B_6, C_7]: (~v2_struct_0(k2_tsep_1(A_5, B_6, C_7)) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~m1_pre_topc(B_6, A_5) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.07/3.87  tff(c_222, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_219, c_10])).
% 10.07/3.87  tff(c_225, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_36, c_222])).
% 10.07/3.87  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_225])).
% 10.07/3.87  tff(c_229, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_207])).
% 10.07/3.87  tff(c_208, plain, (![C_118, D_119, B_120, A_121]: (~r1_tsep_1(C_118, D_119) | r1_tsep_1(B_120, D_119) | ~m1_pre_topc(B_120, C_118) | ~m1_pre_topc(D_119, A_121) | v2_struct_0(D_119) | ~m1_pre_topc(C_118, A_121) | v2_struct_0(C_118) | ~m1_pre_topc(B_120, A_121) | v2_struct_0(B_120) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_212, plain, (![B_120, A_121]: (r1_tsep_1(B_120, '#skF_3') | ~m1_pre_topc(B_120, k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_3', A_121) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_121) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc(B_120, A_121) | v2_struct_0(B_120) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(resolution, [status(thm)], [c_90, c_208])).
% 10.07/3.87  tff(c_218, plain, (![B_120, A_121]: (r1_tsep_1(B_120, '#skF_3') | ~m1_pre_topc(B_120, k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_3', A_121) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_121) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc(B_120, A_121) | v2_struct_0(B_120) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121) | v2_struct_0(A_121))), inference(negUnitSimplification, [status(thm)], [c_42, c_212])).
% 10.07/3.87  tff(c_262, plain, (![B_128, A_129]: (r1_tsep_1(B_128, '#skF_3') | ~m1_pre_topc(B_128, k2_tsep_1('#skF_1', '#skF_2', '#skF_4')) | ~m1_pre_topc('#skF_3', A_129) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_129) | ~m1_pre_topc(B_128, A_129) | v2_struct_0(B_128) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(negUnitSimplification, [status(thm)], [c_229, c_218])).
% 10.07/3.87  tff(c_265, plain, (![C_51, A_129]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', C_51), '#skF_3') | ~m1_pre_topc('#skF_3', A_129) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_129) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_51), A_129) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_51)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129) | ~m1_pre_topc(C_51, '#skF_4') | r1_tsep_1('#skF_2', C_51) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_51, '#skF_1') | v2_struct_0(C_51) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_262])).
% 10.07/3.87  tff(c_277, plain, (![C_51, A_129]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', C_51), '#skF_3') | ~m1_pre_topc('#skF_3', A_129) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_129) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_51), A_129) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_51)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129) | ~m1_pre_topc(C_51, '#skF_4') | r1_tsep_1('#skF_2', C_51) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_51, '#skF_1') | v2_struct_0(C_51) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_36, c_265])).
% 10.07/3.87  tff(c_917, plain, (![C_165, A_166]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', C_165), '#skF_3') | ~m1_pre_topc('#skF_3', A_166) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), A_166) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_165), A_166) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_165)) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166) | ~m1_pre_topc(C_165, '#skF_4') | r1_tsep_1('#skF_2', C_165) | ~m1_pre_topc(C_165, '#skF_1') | v2_struct_0(C_165))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_277])).
% 10.07/3.87  tff(c_932, plain, (![C_165]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', C_165), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_165), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_165)) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_165, '#skF_4') | r1_tsep_1('#skF_2', C_165) | ~m1_pre_topc(C_165, '#skF_1') | v2_struct_0(C_165) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_917])).
% 10.07/3.87  tff(c_951, plain, (![C_165]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', C_165), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_165), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_165)) | ~m1_pre_topc(C_165, '#skF_4') | r1_tsep_1('#skF_2', C_165) | ~m1_pre_topc(C_165, '#skF_1') | v2_struct_0(C_165) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_36, c_50, c_40, c_932])).
% 10.07/3.87  tff(c_953, plain, (![C_167]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', C_167), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_167), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_167)) | ~m1_pre_topc(C_167, '#skF_4') | r1_tsep_1('#skF_2', C_167) | ~m1_pre_topc(C_167, '#skF_1') | v2_struct_0(C_167))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_951])).
% 10.07/3.87  tff(c_16, plain, (![B_14, C_16, A_10]: (~r1_tsep_1(B_14, C_16) | ~m1_pre_topc(B_14, C_16) | ~m1_pre_topc(C_16, A_10) | v2_struct_0(C_16) | ~m1_pre_topc(B_14, A_10) | v2_struct_0(B_14) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.07/3.87  tff(c_963, plain, (![C_167, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_167), '#skF_3') | ~m1_pre_topc('#skF_3', A_10) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_167), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_167), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_167)) | ~m1_pre_topc(C_167, '#skF_4') | r1_tsep_1('#skF_2', C_167) | ~m1_pre_topc(C_167, '#skF_1') | v2_struct_0(C_167))), inference(resolution, [status(thm)], [c_953, c_16])).
% 10.07/3.87  tff(c_1330, plain, (![C_181, A_182]: (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_181), '#skF_3') | ~m1_pre_topc('#skF_3', A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_181), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', C_181), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', C_181)) | ~m1_pre_topc(C_181, '#skF_4') | r1_tsep_1('#skF_2', C_181) | ~m1_pre_topc(C_181, '#skF_1') | v2_struct_0(C_181))), inference(negUnitSimplification, [status(thm)], [c_42, c_963])).
% 10.07/3.87  tff(c_1333, plain, (![A_182]: (~m1_pre_topc('#skF_3', A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_1330])).
% 10.07/3.87  tff(c_1336, plain, (![A_182]: (~m1_pre_topc('#skF_3', A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_40, c_62, c_1333])).
% 10.07/3.87  tff(c_1337, plain, (![A_182]: (~m1_pre_topc('#skF_3', A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_34, c_1336])).
% 10.07/3.87  tff(c_1338, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1337])).
% 10.07/3.87  tff(c_1341, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_1338])).
% 10.07/3.87  tff(c_1344, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_1341])).
% 10.07/3.87  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_1344])).
% 10.07/3.87  tff(c_1348, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_1337])).
% 10.07/3.87  tff(c_1347, plain, (![A_182]: (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_3', A_182) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_182) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(splitRight, [status(thm)], [c_1337])).
% 10.07/3.87  tff(c_1364, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1347])).
% 10.07/3.87  tff(c_1367, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1364, c_10])).
% 10.07/3.87  tff(c_1370, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_1367])).
% 10.07/3.87  tff(c_1372, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_1370])).
% 10.07/3.87  tff(c_1411, plain, (![A_187]: (~m1_pre_topc('#skF_3', A_187) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_187) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(splitRight, [status(thm)], [c_1347])).
% 10.07/3.87  tff(c_1414, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1348, c_1411])).
% 10.07/3.87  tff(c_1437, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_1414])).
% 10.07/3.87  tff(c_1439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_1437])).
% 10.07/3.87  tff(c_1440, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 10.07/3.87  tff(c_1442, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_1440])).
% 10.07/3.87  tff(c_4150, plain, (![A_426, B_427, C_428, D_429]: (m1_pre_topc(k2_tsep_1(A_426, B_427, C_428), k2_tsep_1(A_426, D_429, C_428)) | ~m1_pre_topc(B_427, D_429) | r1_tsep_1(B_427, C_428) | ~m1_pre_topc(D_429, A_426) | v2_struct_0(D_429) | ~m1_pre_topc(C_428, A_426) | v2_struct_0(C_428) | ~m1_pre_topc(B_427, A_426) | v2_struct_0(B_427) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.07/3.87  tff(c_2980, plain, (![A_336, B_337, C_338, D_339]: (m1_pre_topc(k2_tsep_1(A_336, B_337, C_338), k2_tsep_1(A_336, B_337, D_339)) | ~m1_pre_topc(C_338, D_339) | r1_tsep_1(B_337, C_338) | ~m1_pre_topc(D_339, A_336) | v2_struct_0(D_339) | ~m1_pre_topc(C_338, A_336) | v2_struct_0(C_338) | ~m1_pre_topc(B_337, A_336) | v2_struct_0(B_337) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.07/3.87  tff(c_1807, plain, (![A_243, B_244, C_245, D_246]: (m1_pre_topc(k2_tsep_1(A_243, B_244, C_245), k2_tsep_1(A_243, D_246, C_245)) | ~m1_pre_topc(B_244, D_246) | r1_tsep_1(B_244, C_245) | ~m1_pre_topc(D_246, A_243) | v2_struct_0(D_246) | ~m1_pre_topc(C_245, A_243) | v2_struct_0(C_245) | ~m1_pre_topc(B_244, A_243) | v2_struct_0(B_244) | ~l1_pre_topc(A_243) | ~v2_pre_topc(A_243) | v2_struct_0(A_243))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.07/3.87  tff(c_1441, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_56])).
% 10.07/3.87  tff(c_54, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_1457, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1441, c_54])).
% 10.07/3.87  tff(c_1458, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_1457])).
% 10.07/3.87  tff(c_1524, plain, (![D_212, C_213, B_214, A_215]: (~r1_tsep_1(D_212, C_213) | r1_tsep_1(D_212, B_214) | ~m1_pre_topc(B_214, C_213) | ~m1_pre_topc(D_212, A_215) | v2_struct_0(D_212) | ~m1_pre_topc(C_213, A_215) | v2_struct_0(C_213) | ~m1_pre_topc(B_214, A_215) | v2_struct_0(B_214) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_1528, plain, (![B_214, A_215]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), B_214) | ~m1_pre_topc(B_214, '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_215) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_215) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_214, A_215) | v2_struct_0(B_214) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_1458, c_1524])).
% 10.07/3.87  tff(c_1534, plain, (![B_214, A_215]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), B_214) | ~m1_pre_topc(B_214, '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_215) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_215) | ~m1_pre_topc(B_214, A_215) | v2_struct_0(B_214) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(negUnitSimplification, [status(thm)], [c_42, c_1528])).
% 10.07/3.87  tff(c_1536, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1534])).
% 10.07/3.87  tff(c_1539, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1536, c_10])).
% 10.07/3.87  tff(c_1542, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_44, c_1539])).
% 10.07/3.87  tff(c_1544, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_46, c_1542])).
% 10.07/3.87  tff(c_1546, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_1534])).
% 10.07/3.87  tff(c_1676, plain, (![C_228, D_229, B_230, A_231]: (~r1_tsep_1(C_228, D_229) | r1_tsep_1(B_230, D_229) | ~m1_pre_topc(B_230, C_228) | ~m1_pre_topc(D_229, A_231) | v2_struct_0(D_229) | ~m1_pre_topc(C_228, A_231) | v2_struct_0(C_228) | ~m1_pre_topc(B_230, A_231) | v2_struct_0(B_230) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_1684, plain, (![B_230, A_231]: (r1_tsep_1(B_230, '#skF_3') | ~m1_pre_topc(B_230, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_231) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_231) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc(B_230, A_231) | v2_struct_0(B_230) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(resolution, [status(thm)], [c_1458, c_1676])).
% 10.07/3.87  tff(c_1696, plain, (![B_230, A_231]: (r1_tsep_1(B_230, '#skF_3') | ~m1_pre_topc(B_230, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_231) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_231) | ~m1_pre_topc(B_230, A_231) | v2_struct_0(B_230) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231))), inference(negUnitSimplification, [status(thm)], [c_1546, c_42, c_1684])).
% 10.07/3.87  tff(c_1816, plain, (![B_244, A_231]: (r1_tsep_1(k2_tsep_1('#skF_1', B_244, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_231) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_231) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_244, '#skF_2'), A_231) | v2_struct_0(k2_tsep_1('#skF_1', B_244, '#skF_2')) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231) | ~m1_pre_topc(B_244, '#skF_4') | r1_tsep_1(B_244, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_244, '#skF_1') | v2_struct_0(B_244) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1807, c_1696])).
% 10.07/3.87  tff(c_1839, plain, (![B_244, A_231]: (r1_tsep_1(k2_tsep_1('#skF_1', B_244, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_231) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_231) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_244, '#skF_2'), A_231) | v2_struct_0(k2_tsep_1('#skF_1', B_244, '#skF_2')) | ~l1_pre_topc(A_231) | ~v2_pre_topc(A_231) | v2_struct_0(A_231) | ~m1_pre_topc(B_244, '#skF_4') | r1_tsep_1(B_244, '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_244, '#skF_1') | v2_struct_0(B_244) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_36, c_1816])).
% 10.07/3.87  tff(c_1855, plain, (![B_247, A_248]: (r1_tsep_1(k2_tsep_1('#skF_1', B_247, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_248) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_248) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_247, '#skF_2'), A_248) | v2_struct_0(k2_tsep_1('#skF_1', B_247, '#skF_2')) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248) | ~m1_pre_topc(B_247, '#skF_4') | r1_tsep_1(B_247, '#skF_2') | ~m1_pre_topc(B_247, '#skF_1') | v2_struct_0(B_247))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_1839])).
% 10.07/3.87  tff(c_1867, plain, (![B_247]: (r1_tsep_1(k2_tsep_1('#skF_1', B_247, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_247, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_247, '#skF_2')) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_247, '#skF_4') | r1_tsep_1(B_247, '#skF_2') | ~m1_pre_topc(B_247, '#skF_1') | v2_struct_0(B_247) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1855])).
% 10.07/3.87  tff(c_1882, plain, (![B_247]: (r1_tsep_1(k2_tsep_1('#skF_1', B_247, '#skF_2'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_247, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_247, '#skF_2')) | ~m1_pre_topc(B_247, '#skF_4') | r1_tsep_1(B_247, '#skF_2') | ~m1_pre_topc(B_247, '#skF_1') | v2_struct_0(B_247) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_44, c_50, c_40, c_1867])).
% 10.07/3.87  tff(c_1884, plain, (![B_249]: (r1_tsep_1(k2_tsep_1('#skF_1', B_249, '#skF_2'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_249, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_249, '#skF_2')) | ~m1_pre_topc(B_249, '#skF_4') | r1_tsep_1(B_249, '#skF_2') | ~m1_pre_topc(B_249, '#skF_1') | v2_struct_0(B_249))), inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_46, c_1882])).
% 10.07/3.87  tff(c_1894, plain, (![B_249, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_249, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_10) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_249, '#skF_2'), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_249, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_249, '#skF_2')) | ~m1_pre_topc(B_249, '#skF_4') | r1_tsep_1(B_249, '#skF_2') | ~m1_pre_topc(B_249, '#skF_1') | v2_struct_0(B_249))), inference(resolution, [status(thm)], [c_1884, c_16])).
% 10.07/3.87  tff(c_2536, plain, (![B_284, A_285]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_284, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_284, '#skF_2'), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_284, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_284, '#skF_2')) | ~m1_pre_topc(B_284, '#skF_4') | r1_tsep_1(B_284, '#skF_2') | ~m1_pre_topc(B_284, '#skF_1') | v2_struct_0(B_284))), inference(negUnitSimplification, [status(thm)], [c_42, c_1894])).
% 10.07/3.87  tff(c_2539, plain, (![A_285]: (~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4') | r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_2536])).
% 10.07/3.87  tff(c_2542, plain, (![A_285]: (~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_44, c_62, c_2539])).
% 10.07/3.87  tff(c_2543, plain, (![A_285]: (~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_2542])).
% 10.07/3.87  tff(c_2545, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_2543])).
% 10.07/3.87  tff(c_2548, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_2545])).
% 10.07/3.87  tff(c_2551, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_2548])).
% 10.07/3.87  tff(c_2553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_2551])).
% 10.07/3.87  tff(c_2555, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_2543])).
% 10.07/3.87  tff(c_63, plain, (![B_66, A_67]: (l1_pre_topc(B_66) | ~m1_pre_topc(B_66, A_67) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.07/3.87  tff(c_69, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_63])).
% 10.07/3.87  tff(c_79, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_69])).
% 10.07/3.87  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.07/3.87  tff(c_72, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_63])).
% 10.07/3.87  tff(c_82, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_72])).
% 10.07/3.87  tff(c_1451, plain, (![A_194, B_195, C_196]: (m1_pre_topc(k2_tsep_1(A_194, B_195, C_196), A_194) | ~m1_pre_topc(C_196, A_194) | v2_struct_0(C_196) | ~m1_pre_topc(B_195, A_194) | v2_struct_0(B_195) | ~l1_pre_topc(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.07/3.87  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.07/3.87  tff(c_1455, plain, (![A_194, B_195, C_196]: (l1_pre_topc(k2_tsep_1(A_194, B_195, C_196)) | ~m1_pre_topc(C_196, A_194) | v2_struct_0(C_196) | ~m1_pre_topc(B_195, A_194) | v2_struct_0(B_195) | ~l1_pre_topc(A_194) | v2_struct_0(A_194))), inference(resolution, [status(thm)], [c_1451, c_4])).
% 10.07/3.87  tff(c_12, plain, (![B_9, A_8]: (r1_tsep_1(B_9, A_8) | ~r1_tsep_1(A_8, B_9) | ~l1_struct_0(B_9) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.07/3.87  tff(c_1461, plain, (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~l1_struct_0('#skF_3') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_1458, c_12])).
% 10.07/3.87  tff(c_1462, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_1461])).
% 10.07/3.87  tff(c_1466, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_1462])).
% 10.07/3.87  tff(c_1469, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1455, c_1466])).
% 10.07/3.87  tff(c_1472, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_44, c_1469])).
% 10.07/3.87  tff(c_1474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_46, c_1472])).
% 10.07/3.87  tff(c_1475, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_1461])).
% 10.07/3.87  tff(c_1483, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_1475])).
% 10.07/3.87  tff(c_1486, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_1483])).
% 10.07/3.87  tff(c_1490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_1486])).
% 10.07/3.87  tff(c_1492, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_1475])).
% 10.07/3.87  tff(c_2554, plain, (![A_285]: (r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(splitRight, [status(thm)], [c_2543])).
% 10.07/3.87  tff(c_2570, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2554])).
% 10.07/3.87  tff(c_2573, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2570, c_10])).
% 10.07/3.87  tff(c_2576, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_2573])).
% 10.07/3.87  tff(c_2578, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_2576])).
% 10.07/3.87  tff(c_2579, plain, (![A_285]: (r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', A_285) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_285) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(splitRight, [status(thm)], [c_2554])).
% 10.07/3.87  tff(c_2581, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_2579])).
% 10.07/3.87  tff(c_2597, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2581, c_12])).
% 10.07/3.87  tff(c_2616, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1492, c_2597])).
% 10.07/3.87  tff(c_2617, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_2616])).
% 10.07/3.87  tff(c_2620, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_2617])).
% 10.07/3.87  tff(c_2624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_2620])).
% 10.07/3.87  tff(c_2627, plain, (![A_290]: (~m1_pre_topc('#skF_3', A_290) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_290) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290) | v2_struct_0(A_290))), inference(splitRight, [status(thm)], [c_2579])).
% 10.07/3.87  tff(c_2630, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2555, c_2627])).
% 10.07/3.87  tff(c_2653, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_2630])).
% 10.07/3.87  tff(c_2655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2653])).
% 10.07/3.87  tff(c_2656, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_1457])).
% 10.07/3.87  tff(c_2658, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_2656])).
% 10.07/3.87  tff(c_2754, plain, (![D_314, C_315, B_316, A_317]: (~r1_tsep_1(D_314, C_315) | r1_tsep_1(B_316, D_314) | ~m1_pre_topc(B_316, C_315) | ~m1_pre_topc(D_314, A_317) | v2_struct_0(D_314) | ~m1_pre_topc(C_315, A_317) | v2_struct_0(C_315) | ~m1_pre_topc(B_316, A_317) | v2_struct_0(B_316) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | v2_struct_0(A_317))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_2758, plain, (![B_316, A_317]: (r1_tsep_1(B_316, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_316, '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_317) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_317) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_316, A_317) | v2_struct_0(B_316) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | v2_struct_0(A_317))), inference(resolution, [status(thm)], [c_2658, c_2754])).
% 10.07/3.87  tff(c_2764, plain, (![B_316, A_317]: (r1_tsep_1(B_316, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_316, '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_317) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_317) | ~m1_pre_topc(B_316, A_317) | v2_struct_0(B_316) | ~l1_pre_topc(A_317) | ~v2_pre_topc(A_317) | v2_struct_0(A_317))), inference(negUnitSimplification, [status(thm)], [c_46, c_2758])).
% 10.07/3.87  tff(c_2776, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2764])).
% 10.07/3.87  tff(c_2779, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_2776, c_10])).
% 10.07/3.87  tff(c_2782, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_2779])).
% 10.07/3.87  tff(c_2784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_2782])).
% 10.07/3.87  tff(c_2786, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2764])).
% 10.07/3.87  tff(c_2765, plain, (![C_318, D_319, B_320, A_321]: (~r1_tsep_1(C_318, D_319) | r1_tsep_1(D_319, B_320) | ~m1_pre_topc(B_320, C_318) | ~m1_pre_topc(D_319, A_321) | v2_struct_0(D_319) | ~m1_pre_topc(C_318, A_321) | v2_struct_0(C_318) | ~m1_pre_topc(B_320, A_321) | v2_struct_0(B_320) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_2769, plain, (![B_320, A_321]: (r1_tsep_1('#skF_2', B_320) | ~m1_pre_topc(B_320, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_321) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_321) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_320, A_321) | v2_struct_0(B_320) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(resolution, [status(thm)], [c_2658, c_2765])).
% 10.07/3.87  tff(c_2775, plain, (![B_320, A_321]: (r1_tsep_1('#skF_2', B_320) | ~m1_pre_topc(B_320, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_321) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_321) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_320, A_321) | v2_struct_0(B_320) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(negUnitSimplification, [status(thm)], [c_46, c_2769])).
% 10.07/3.87  tff(c_2787, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2775])).
% 10.07/3.87  tff(c_2788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2786, c_2787])).
% 10.07/3.87  tff(c_2789, plain, (![B_320, A_321]: (r1_tsep_1('#skF_2', B_320) | ~m1_pre_topc(B_320, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_321) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_321) | ~m1_pre_topc(B_320, A_321) | v2_struct_0(B_320) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(splitRight, [status(thm)], [c_2775])).
% 10.07/3.87  tff(c_2989, plain, (![C_338, A_321]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_338)) | ~m1_pre_topc('#skF_2', A_321) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_321) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_338), A_321) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_338)) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321) | ~m1_pre_topc(C_338, '#skF_4') | r1_tsep_1('#skF_3', C_338) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_338, '#skF_1') | v2_struct_0(C_338) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_2980, c_2789])).
% 10.07/3.87  tff(c_3006, plain, (![C_338, A_321]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_338)) | ~m1_pre_topc('#skF_2', A_321) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_321) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_338), A_321) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_338)) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321) | ~m1_pre_topc(C_338, '#skF_4') | r1_tsep_1('#skF_3', C_338) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_338, '#skF_1') | v2_struct_0(C_338) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_36, c_2989])).
% 10.07/3.87  tff(c_3561, plain, (![C_368, A_369]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_368)) | ~m1_pre_topc('#skF_2', A_369) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_369) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_368), A_369) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_368)) | ~l1_pre_topc(A_369) | ~v2_pre_topc(A_369) | v2_struct_0(A_369) | ~m1_pre_topc(C_368, '#skF_4') | r1_tsep_1('#skF_3', C_368) | ~m1_pre_topc(C_368, '#skF_1') | v2_struct_0(C_368))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_3006])).
% 10.07/3.87  tff(c_3576, plain, (![C_368]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_368)) | ~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_368), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_368)) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_368, '#skF_4') | r1_tsep_1('#skF_3', C_368) | ~m1_pre_topc(C_368, '#skF_1') | v2_struct_0(C_368) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_3561])).
% 10.07/3.87  tff(c_3595, plain, (![C_368]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_368)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_368), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_368)) | ~m1_pre_topc(C_368, '#skF_4') | r1_tsep_1('#skF_3', C_368) | ~m1_pre_topc(C_368, '#skF_1') | v2_struct_0(C_368) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_50, c_44, c_3576])).
% 10.07/3.87  tff(c_3597, plain, (![C_370]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_370)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_370), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_370)) | ~m1_pre_topc(C_370, '#skF_4') | r1_tsep_1('#skF_3', C_370) | ~m1_pre_topc(C_370, '#skF_1') | v2_struct_0(C_370))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_3595])).
% 10.07/3.87  tff(c_14, plain, (![C_16, B_14, A_10]: (~r1_tsep_1(C_16, B_14) | ~m1_pre_topc(B_14, C_16) | ~m1_pre_topc(C_16, A_10) | v2_struct_0(C_16) | ~m1_pre_topc(B_14, A_10) | v2_struct_0(B_14) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_93])).
% 10.07/3.87  tff(c_3607, plain, (![C_370, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_370), '#skF_2') | ~m1_pre_topc('#skF_2', A_10) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_370), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_370), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_370)) | ~m1_pre_topc(C_370, '#skF_4') | r1_tsep_1('#skF_3', C_370) | ~m1_pre_topc(C_370, '#skF_1') | v2_struct_0(C_370))), inference(resolution, [status(thm)], [c_3597, c_14])).
% 10.07/3.87  tff(c_3696, plain, (![C_374, A_375]: (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_374), '#skF_2') | ~m1_pre_topc('#skF_2', A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_374), A_375) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_374), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_374)) | ~m1_pre_topc(C_374, '#skF_4') | r1_tsep_1('#skF_3', C_374) | ~m1_pre_topc(C_374, '#skF_1') | v2_struct_0(C_374))), inference(negUnitSimplification, [status(thm)], [c_46, c_3607])).
% 10.07/3.87  tff(c_3699, plain, (![A_375]: (~m1_pre_topc('#skF_2', A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_375) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_3696])).
% 10.07/3.87  tff(c_3702, plain, (![A_375]: (~m1_pre_topc('#skF_2', A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_375) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_44, c_1442, c_3699])).
% 10.07/3.87  tff(c_3703, plain, (![A_375]: (~m1_pre_topc('#skF_2', A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_375) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_3702])).
% 10.07/3.87  tff(c_3704, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_3703])).
% 10.07/3.87  tff(c_3707, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_3704])).
% 10.07/3.87  tff(c_3710, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_3707])).
% 10.07/3.87  tff(c_3712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_3710])).
% 10.07/3.87  tff(c_3714, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_3703])).
% 10.07/3.87  tff(c_2661, plain, (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~l1_struct_0('#skF_2') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2658, c_12])).
% 10.07/3.87  tff(c_2662, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_2661])).
% 10.07/3.87  tff(c_2672, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_2662])).
% 10.07/3.87  tff(c_2675, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1455, c_2672])).
% 10.07/3.87  tff(c_2678, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_2675])).
% 10.07/3.87  tff(c_2680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_2678])).
% 10.07/3.87  tff(c_2681, plain, (~l1_struct_0('#skF_2') | r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_2661])).
% 10.07/3.87  tff(c_2683, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_2681])).
% 10.07/3.87  tff(c_2686, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_2683])).
% 10.07/3.87  tff(c_2690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_2686])).
% 10.07/3.87  tff(c_2692, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_2681])).
% 10.07/3.87  tff(c_3713, plain, (![A_375]: (r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_2', A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_375) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(splitRight, [status(thm)], [c_3703])).
% 10.07/3.87  tff(c_3730, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3713])).
% 10.07/3.87  tff(c_3775, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3730, c_10])).
% 10.07/3.87  tff(c_3778, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_3775])).
% 10.07/3.87  tff(c_3780, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_3778])).
% 10.07/3.87  tff(c_3781, plain, (![A_375]: (r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', A_375) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_375) | ~l1_pre_topc(A_375) | ~v2_pre_topc(A_375) | v2_struct_0(A_375))), inference(splitRight, [status(thm)], [c_3713])).
% 10.07/3.87  tff(c_3783, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_3781])).
% 10.07/3.87  tff(c_3797, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_3783, c_12])).
% 10.07/3.87  tff(c_3816, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2692, c_3797])).
% 10.07/3.87  tff(c_3817, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_3816])).
% 10.07/3.87  tff(c_3820, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_3817])).
% 10.07/3.87  tff(c_3824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_3820])).
% 10.07/3.87  tff(c_3829, plain, (![A_382]: (~m1_pre_topc('#skF_2', A_382) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_382) | ~l1_pre_topc(A_382) | ~v2_pre_topc(A_382) | v2_struct_0(A_382))), inference(splitRight, [status(thm)], [c_3781])).
% 10.07/3.87  tff(c_3832, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3714, c_3829])).
% 10.07/3.87  tff(c_3855, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_3832])).
% 10.07/3.87  tff(c_3857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3855])).
% 10.07/3.87  tff(c_3858, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_2656])).
% 10.07/3.87  tff(c_3955, plain, (![C_406, D_407, B_408, A_409]: (~r1_tsep_1(C_406, D_407) | r1_tsep_1(D_407, B_408) | ~m1_pre_topc(B_408, C_406) | ~m1_pre_topc(D_407, A_409) | v2_struct_0(D_407) | ~m1_pre_topc(C_406, A_409) | v2_struct_0(C_406) | ~m1_pre_topc(B_408, A_409) | v2_struct_0(B_408) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_3959, plain, (![B_408, A_409]: (r1_tsep_1('#skF_2', B_408) | ~m1_pre_topc(B_408, k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_409) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_409) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_408, A_409) | v2_struct_0(B_408) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409))), inference(resolution, [status(thm)], [c_3858, c_3955])).
% 10.07/3.87  tff(c_3965, plain, (![B_408, A_409]: (r1_tsep_1('#skF_2', B_408) | ~m1_pre_topc(B_408, k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_409) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_409) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_408, A_409) | v2_struct_0(B_408) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409))), inference(negUnitSimplification, [status(thm)], [c_46, c_3959])).
% 10.07/3.87  tff(c_3977, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3965])).
% 10.07/3.87  tff(c_3980, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3977, c_10])).
% 10.07/3.87  tff(c_3983, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_40, c_3980])).
% 10.07/3.87  tff(c_3985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_42, c_3983])).
% 10.07/3.87  tff(c_3986, plain, (![B_408, A_409]: (r1_tsep_1('#skF_2', B_408) | ~m1_pre_topc(B_408, k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_409) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_409) | ~m1_pre_topc(B_408, A_409) | v2_struct_0(B_408) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409))), inference(splitRight, [status(thm)], [c_3965])).
% 10.07/3.87  tff(c_4159, plain, (![B_427, A_409]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_427, '#skF_3')) | ~m1_pre_topc('#skF_2', A_409) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_409) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_427, '#skF_3'), A_409) | v2_struct_0(k2_tsep_1('#skF_1', B_427, '#skF_3')) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409) | ~m1_pre_topc(B_427, '#skF_4') | r1_tsep_1(B_427, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_427, '#skF_1') | v2_struct_0(B_427) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4150, c_3986])).
% 10.07/3.87  tff(c_4173, plain, (![B_427, A_409]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_427, '#skF_3')) | ~m1_pre_topc('#skF_2', A_409) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_409) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_427, '#skF_3'), A_409) | v2_struct_0(k2_tsep_1('#skF_1', B_427, '#skF_3')) | ~l1_pre_topc(A_409) | ~v2_pre_topc(A_409) | v2_struct_0(A_409) | ~m1_pre_topc(B_427, '#skF_4') | r1_tsep_1(B_427, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_427, '#skF_1') | v2_struct_0(B_427) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_36, c_4159])).
% 10.07/3.87  tff(c_4759, plain, (![B_460, A_461]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_460, '#skF_3')) | ~m1_pre_topc('#skF_2', A_461) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_461) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_460, '#skF_3'), A_461) | v2_struct_0(k2_tsep_1('#skF_1', B_460, '#skF_3')) | ~l1_pre_topc(A_461) | ~v2_pre_topc(A_461) | v2_struct_0(A_461) | ~m1_pre_topc(B_460, '#skF_4') | r1_tsep_1(B_460, '#skF_3') | ~m1_pre_topc(B_460, '#skF_1') | v2_struct_0(B_460))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_4173])).
% 10.07/3.87  tff(c_4774, plain, (![B_460]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_460, '#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_460, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_460, '#skF_3')) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_460, '#skF_4') | r1_tsep_1(B_460, '#skF_3') | ~m1_pre_topc(B_460, '#skF_1') | v2_struct_0(B_460) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_4759])).
% 10.07/3.87  tff(c_4793, plain, (![B_460]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_460, '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_460, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_460, '#skF_3')) | ~m1_pre_topc(B_460, '#skF_4') | r1_tsep_1(B_460, '#skF_3') | ~m1_pre_topc(B_460, '#skF_1') | v2_struct_0(B_460) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_40, c_50, c_44, c_4774])).
% 10.07/3.87  tff(c_4795, plain, (![B_462]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_462, '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_462, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_462, '#skF_3')) | ~m1_pre_topc(B_462, '#skF_4') | r1_tsep_1(B_462, '#skF_3') | ~m1_pre_topc(B_462, '#skF_1') | v2_struct_0(B_462))), inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_42, c_4793])).
% 10.07/3.87  tff(c_4805, plain, (![B_462, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_462, '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_2', A_10) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_462, '#skF_3'), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_462, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_462, '#skF_3')) | ~m1_pre_topc(B_462, '#skF_4') | r1_tsep_1(B_462, '#skF_3') | ~m1_pre_topc(B_462, '#skF_1') | v2_struct_0(B_462))), inference(resolution, [status(thm)], [c_4795, c_14])).
% 10.07/3.87  tff(c_5012, plain, (![B_476, A_477]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_476, '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_2', A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_476, '#skF_3'), A_477) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_476, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_476, '#skF_3')) | ~m1_pre_topc(B_476, '#skF_4') | r1_tsep_1(B_476, '#skF_3') | ~m1_pre_topc(B_476, '#skF_1') | v2_struct_0(B_476))), inference(negUnitSimplification, [status(thm)], [c_46, c_4805])).
% 10.07/3.87  tff(c_5015, plain, (![A_477]: (~m1_pre_topc('#skF_2', A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_477) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_5012])).
% 10.07/3.87  tff(c_5018, plain, (![A_477]: (~m1_pre_topc('#skF_2', A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_477) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_40, c_1442, c_5015])).
% 10.07/3.87  tff(c_5019, plain, (![A_477]: (~m1_pre_topc('#skF_2', A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_477) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_34, c_5018])).
% 10.07/3.87  tff(c_5022, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_5019])).
% 10.07/3.87  tff(c_5025, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_5022])).
% 10.07/3.87  tff(c_5028, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_5025])).
% 10.07/3.87  tff(c_5030, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_5028])).
% 10.07/3.87  tff(c_5032, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_5019])).
% 10.07/3.87  tff(c_5031, plain, (![A_477]: (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_2', A_477) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_477) | ~l1_pre_topc(A_477) | ~v2_pre_topc(A_477) | v2_struct_0(A_477))), inference(splitRight, [status(thm)], [c_5019])).
% 10.07/3.87  tff(c_5047, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_5031])).
% 10.07/3.87  tff(c_5050, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5047, c_10])).
% 10.07/3.87  tff(c_5053, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_5050])).
% 10.07/3.87  tff(c_5055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_5053])).
% 10.07/3.87  tff(c_5058, plain, (![A_480]: (~m1_pre_topc('#skF_2', A_480) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_480) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(splitRight, [status(thm)], [c_5031])).
% 10.07/3.87  tff(c_5061, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5032, c_5058])).
% 10.07/3.87  tff(c_5084, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_5061])).
% 10.07/3.87  tff(c_5086, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_5084])).
% 10.07/3.87  tff(c_5087, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_1440])).
% 10.07/3.87  tff(c_5187, plain, (![D_521, C_522, B_523, A_524]: (~r1_tsep_1(D_521, C_522) | r1_tsep_1(B_523, D_521) | ~m1_pre_topc(B_523, C_522) | ~m1_pre_topc(D_521, A_524) | v2_struct_0(D_521) | ~m1_pre_topc(C_522, A_524) | v2_struct_0(C_522) | ~m1_pre_topc(B_523, A_524) | v2_struct_0(B_523) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_5191, plain, (![B_523, A_524]: (r1_tsep_1(B_523, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc(B_523, '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_524) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_524) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_523, A_524) | v2_struct_0(B_523) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(resolution, [status(thm)], [c_5087, c_5187])).
% 10.07/3.87  tff(c_5197, plain, (![B_523, A_524]: (r1_tsep_1(B_523, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc(B_523, '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_524) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_524) | ~m1_pre_topc(B_523, A_524) | v2_struct_0(B_523) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(negUnitSimplification, [status(thm)], [c_42, c_5191])).
% 10.07/3.87  tff(c_5220, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5197])).
% 10.07/3.87  tff(c_5223, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5220, c_10])).
% 10.07/3.87  tff(c_5226, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_44, c_5223])).
% 10.07/3.87  tff(c_5228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_46, c_5226])).
% 10.07/3.87  tff(c_5230, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_5197])).
% 10.07/3.87  tff(c_5209, plain, (![C_529, D_530, B_531, A_532]: (~r1_tsep_1(C_529, D_530) | r1_tsep_1(D_530, B_531) | ~m1_pre_topc(B_531, C_529) | ~m1_pre_topc(D_530, A_532) | v2_struct_0(D_530) | ~m1_pre_topc(C_529, A_532) | v2_struct_0(C_529) | ~m1_pre_topc(B_531, A_532) | v2_struct_0(B_531) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_5213, plain, (![B_531, A_532]: (r1_tsep_1('#skF_3', B_531) | ~m1_pre_topc(B_531, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_532) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_532) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc(B_531, A_532) | v2_struct_0(B_531) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532))), inference(resolution, [status(thm)], [c_5087, c_5209])).
% 10.07/3.87  tff(c_5219, plain, (![B_531, A_532]: (r1_tsep_1('#skF_3', B_531) | ~m1_pre_topc(B_531, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_532) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_532) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc(B_531, A_532) | v2_struct_0(B_531) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532))), inference(negUnitSimplification, [status(thm)], [c_42, c_5213])).
% 10.07/3.87  tff(c_5529, plain, (![B_554, A_555]: (r1_tsep_1('#skF_3', B_554) | ~m1_pre_topc(B_554, k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~m1_pre_topc('#skF_3', A_555) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_555) | ~m1_pre_topc(B_554, A_555) | v2_struct_0(B_554) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555))), inference(negUnitSimplification, [status(thm)], [c_5230, c_5219])).
% 10.07/3.87  tff(c_5535, plain, (![B_47, A_555]: (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', B_47, '#skF_2')) | ~m1_pre_topc('#skF_3', A_555) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_555) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_47, '#skF_2'), A_555) | v2_struct_0(k2_tsep_1('#skF_1', B_47, '#skF_2')) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555) | ~m1_pre_topc(B_47, '#skF_4') | r1_tsep_1(B_47, '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_47, '#skF_1') | v2_struct_0(B_47) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_5529])).
% 10.07/3.87  tff(c_5551, plain, (![B_47, A_555]: (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', B_47, '#skF_2')) | ~m1_pre_topc('#skF_3', A_555) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_555) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_47, '#skF_2'), A_555) | v2_struct_0(k2_tsep_1('#skF_1', B_47, '#skF_2')) | ~l1_pre_topc(A_555) | ~v2_pre_topc(A_555) | v2_struct_0(A_555) | ~m1_pre_topc(B_47, '#skF_4') | r1_tsep_1(B_47, '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_47, '#skF_1') | v2_struct_0(B_47) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_36, c_5535])).
% 10.07/3.87  tff(c_5990, plain, (![B_579, A_580]: (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', B_579, '#skF_2')) | ~m1_pre_topc('#skF_3', A_580) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'), A_580) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_579, '#skF_2'), A_580) | v2_struct_0(k2_tsep_1('#skF_1', B_579, '#skF_2')) | ~l1_pre_topc(A_580) | ~v2_pre_topc(A_580) | v2_struct_0(A_580) | ~m1_pre_topc(B_579, '#skF_4') | r1_tsep_1(B_579, '#skF_2') | ~m1_pre_topc(B_579, '#skF_1') | v2_struct_0(B_579))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_38, c_5551])).
% 10.07/3.87  tff(c_6005, plain, (![B_579]: (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', B_579, '#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_579, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_579, '#skF_2')) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_579, '#skF_4') | r1_tsep_1(B_579, '#skF_2') | ~m1_pre_topc(B_579, '#skF_1') | v2_struct_0(B_579) | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_5990])).
% 10.07/3.87  tff(c_6024, plain, (![B_579]: (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', B_579, '#skF_2')) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_579, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_579, '#skF_2')) | ~m1_pre_topc(B_579, '#skF_4') | r1_tsep_1(B_579, '#skF_2') | ~m1_pre_topc(B_579, '#skF_1') | v2_struct_0(B_579) | v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_44, c_50, c_40, c_6005])).
% 10.07/3.87  tff(c_6026, plain, (![B_581]: (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', B_581, '#skF_2')) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_581, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_581, '#skF_2')) | ~m1_pre_topc(B_581, '#skF_4') | r1_tsep_1(B_581, '#skF_2') | ~m1_pre_topc(B_581, '#skF_1') | v2_struct_0(B_581))), inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_46, c_6024])).
% 10.07/3.87  tff(c_6036, plain, (![B_581, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_581, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_10) | v2_struct_0('#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_581, '#skF_2'), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_581, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_581, '#skF_2')) | ~m1_pre_topc(B_581, '#skF_4') | r1_tsep_1(B_581, '#skF_2') | ~m1_pre_topc(B_581, '#skF_1') | v2_struct_0(B_581))), inference(resolution, [status(thm)], [c_6026, c_14])).
% 10.07/3.87  tff(c_6321, plain, (![B_597, A_598]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_597, '#skF_2'), '#skF_3') | ~m1_pre_topc('#skF_3', A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_597, '#skF_2'), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_597, '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_597, '#skF_2')) | ~m1_pre_topc(B_597, '#skF_4') | r1_tsep_1(B_597, '#skF_2') | ~m1_pre_topc(B_597, '#skF_1') | v2_struct_0(B_597))), inference(negUnitSimplification, [status(thm)], [c_42, c_6036])).
% 10.07/3.87  tff(c_6324, plain, (![A_598]: (~m1_pre_topc('#skF_3', A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_3', '#skF_4') | r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_6321])).
% 10.07/3.87  tff(c_6327, plain, (![A_598]: (~m1_pre_topc('#skF_3', A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_44, c_62, c_6324])).
% 10.07/3.87  tff(c_6328, plain, (![A_598]: (~m1_pre_topc('#skF_3', A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_6327])).
% 10.07/3.87  tff(c_6329, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_6328])).
% 10.07/3.87  tff(c_6332, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_6329])).
% 10.07/3.87  tff(c_6335, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_6332])).
% 10.07/3.87  tff(c_6337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_6335])).
% 10.07/3.87  tff(c_6339, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_6328])).
% 10.07/3.87  tff(c_5101, plain, (![A_487, B_488, C_489]: (m1_pre_topc(k2_tsep_1(A_487, B_488, C_489), A_487) | ~m1_pre_topc(C_489, A_487) | v2_struct_0(C_489) | ~m1_pre_topc(B_488, A_487) | v2_struct_0(B_488) | ~l1_pre_topc(A_487) | v2_struct_0(A_487))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.07/3.87  tff(c_5106, plain, (![A_490, B_491, C_492]: (l1_pre_topc(k2_tsep_1(A_490, B_491, C_492)) | ~m1_pre_topc(C_492, A_490) | v2_struct_0(C_492) | ~m1_pre_topc(B_491, A_490) | v2_struct_0(B_491) | ~l1_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_5101, c_4])).
% 10.07/3.87  tff(c_5091, plain, (r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', '#skF_4', '#skF_2')) | ~l1_struct_0('#skF_3') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_5087, c_12])).
% 10.07/3.87  tff(c_5092, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5091])).
% 10.07/3.87  tff(c_5096, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_2, c_5092])).
% 10.07/3.87  tff(c_5109, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_5106, c_5096])).
% 10.07/3.87  tff(c_5112, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_44, c_5109])).
% 10.07/3.87  tff(c_5114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_46, c_5112])).
% 10.07/3.87  tff(c_5115, plain, (~l1_struct_0('#skF_3') | r1_tsep_1('#skF_3', k2_tsep_1('#skF_1', '#skF_4', '#skF_2'))), inference(splitRight, [status(thm)], [c_5091])).
% 10.07/3.87  tff(c_5118, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_5115])).
% 10.07/3.87  tff(c_5121, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_5118])).
% 10.07/3.87  tff(c_5125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_5121])).
% 10.07/3.87  tff(c_5127, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_5115])).
% 10.07/3.87  tff(c_6338, plain, (![A_598]: (r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_3', A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(splitRight, [status(thm)], [c_6328])).
% 10.07/3.87  tff(c_6356, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_6338])).
% 10.07/3.87  tff(c_6359, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6356, c_10])).
% 10.07/3.87  tff(c_6362, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_6359])).
% 10.07/3.87  tff(c_6364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_6362])).
% 10.07/3.87  tff(c_6365, plain, (![A_598]: (r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', A_598) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_598) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(splitRight, [status(thm)], [c_6338])).
% 10.07/3.87  tff(c_6367, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_6365])).
% 10.07/3.87  tff(c_6381, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_6367, c_12])).
% 10.07/3.87  tff(c_6400, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5127, c_6381])).
% 10.07/3.87  tff(c_6401, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_6400])).
% 10.07/3.87  tff(c_6404, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_6401])).
% 10.07/3.87  tff(c_6408, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_6404])).
% 10.07/3.87  tff(c_6413, plain, (![A_603]: (~m1_pre_topc('#skF_3', A_603) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_603) | ~l1_pre_topc(A_603) | ~v2_pre_topc(A_603) | v2_struct_0(A_603))), inference(splitRight, [status(thm)], [c_6365])).
% 10.07/3.87  tff(c_6416, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6339, c_6413])).
% 10.07/3.87  tff(c_6439, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_6416])).
% 10.07/3.87  tff(c_6441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_6439])).
% 10.07/3.87  tff(c_6442, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 10.07/3.87  tff(c_6844, plain, (![A_678, B_679, C_680, D_681]: (m1_pre_topc(k2_tsep_1(A_678, B_679, C_680), k2_tsep_1(A_678, D_681, C_680)) | ~m1_pre_topc(B_679, D_681) | r1_tsep_1(B_679, C_680) | ~m1_pre_topc(D_681, A_678) | v2_struct_0(D_681) | ~m1_pre_topc(C_680, A_678) | v2_struct_0(C_680) | ~m1_pre_topc(B_679, A_678) | v2_struct_0(B_679) | ~l1_pre_topc(A_678) | ~v2_pre_topc(A_678) | v2_struct_0(A_678))), inference(cnfTransformation, [status(thm)], [f_192])).
% 10.07/3.87  tff(c_6443, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 10.07/3.87  tff(c_58, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2') | m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 10.07/3.87  tff(c_6471, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_6443, c_58])).
% 10.07/3.87  tff(c_6472, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_6471])).
% 10.07/3.87  tff(c_6565, plain, (![D_647, C_648, B_649, A_650]: (~r1_tsep_1(D_647, C_648) | r1_tsep_1(D_647, B_649) | ~m1_pre_topc(B_649, C_648) | ~m1_pre_topc(D_647, A_650) | v2_struct_0(D_647) | ~m1_pre_topc(C_648, A_650) | v2_struct_0(C_648) | ~m1_pre_topc(B_649, A_650) | v2_struct_0(B_649) | ~l1_pre_topc(A_650) | ~v2_pre_topc(A_650) | v2_struct_0(A_650))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_6569, plain, (![B_649, A_650]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), B_649) | ~m1_pre_topc(B_649, '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_650) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_650) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_649, A_650) | v2_struct_0(B_649) | ~l1_pre_topc(A_650) | ~v2_pre_topc(A_650) | v2_struct_0(A_650))), inference(resolution, [status(thm)], [c_6472, c_6565])).
% 10.07/3.87  tff(c_6575, plain, (![B_649, A_650]: (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), B_649) | ~m1_pre_topc(B_649, '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_650) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_650) | ~m1_pre_topc(B_649, A_650) | v2_struct_0(B_649) | ~l1_pre_topc(A_650) | ~v2_pre_topc(A_650) | v2_struct_0(A_650))), inference(negUnitSimplification, [status(thm)], [c_46, c_6569])).
% 10.07/3.87  tff(c_6576, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6575])).
% 10.07/3.87  tff(c_6579, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6576, c_10])).
% 10.07/3.87  tff(c_6582, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_40, c_6579])).
% 10.07/3.87  tff(c_6584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_42, c_6582])).
% 10.07/3.87  tff(c_6586, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_6575])).
% 10.07/3.87  tff(c_6804, plain, (![C_672, D_673, B_674, A_675]: (~r1_tsep_1(C_672, D_673) | r1_tsep_1(D_673, B_674) | ~m1_pre_topc(B_674, C_672) | ~m1_pre_topc(D_673, A_675) | v2_struct_0(D_673) | ~m1_pre_topc(C_672, A_675) | v2_struct_0(C_672) | ~m1_pre_topc(B_674, A_675) | v2_struct_0(B_674) | ~l1_pre_topc(A_675) | ~v2_pre_topc(A_675) | v2_struct_0(A_675))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_6812, plain, (![B_674, A_675]: (r1_tsep_1('#skF_2', B_674) | ~m1_pre_topc(B_674, k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_675) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_675) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc(B_674, A_675) | v2_struct_0(B_674) | ~l1_pre_topc(A_675) | ~v2_pre_topc(A_675) | v2_struct_0(A_675))), inference(resolution, [status(thm)], [c_6472, c_6804])).
% 10.07/3.87  tff(c_6823, plain, (![B_674, A_675]: (r1_tsep_1('#skF_2', B_674) | ~m1_pre_topc(B_674, k2_tsep_1('#skF_1', '#skF_4', '#skF_3')) | ~m1_pre_topc('#skF_2', A_675) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_675) | ~m1_pre_topc(B_674, A_675) | v2_struct_0(B_674) | ~l1_pre_topc(A_675) | ~v2_pre_topc(A_675) | v2_struct_0(A_675))), inference(negUnitSimplification, [status(thm)], [c_6586, c_46, c_6812])).
% 10.07/3.87  tff(c_6847, plain, (![B_679, A_675]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_679, '#skF_3')) | ~m1_pre_topc('#skF_2', A_675) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_675) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_679, '#skF_3'), A_675) | v2_struct_0(k2_tsep_1('#skF_1', B_679, '#skF_3')) | ~l1_pre_topc(A_675) | ~v2_pre_topc(A_675) | v2_struct_0(A_675) | ~m1_pre_topc(B_679, '#skF_4') | r1_tsep_1(B_679, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_679, '#skF_1') | v2_struct_0(B_679) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6844, c_6823])).
% 10.07/3.87  tff(c_6868, plain, (![B_679, A_675]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_679, '#skF_3')) | ~m1_pre_topc('#skF_2', A_675) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_675) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_679, '#skF_3'), A_675) | v2_struct_0(k2_tsep_1('#skF_1', B_679, '#skF_3')) | ~l1_pre_topc(A_675) | ~v2_pre_topc(A_675) | v2_struct_0(A_675) | ~m1_pre_topc(B_679, '#skF_4') | r1_tsep_1(B_679, '#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~m1_pre_topc(B_679, '#skF_1') | v2_struct_0(B_679) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_36, c_6847])).
% 10.07/3.87  tff(c_7039, plain, (![B_695, A_696]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_695, '#skF_3')) | ~m1_pre_topc('#skF_2', A_696) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_4', '#skF_3'), A_696) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_695, '#skF_3'), A_696) | v2_struct_0(k2_tsep_1('#skF_1', B_695, '#skF_3')) | ~l1_pre_topc(A_696) | ~v2_pre_topc(A_696) | v2_struct_0(A_696) | ~m1_pre_topc(B_695, '#skF_4') | r1_tsep_1(B_695, '#skF_3') | ~m1_pre_topc(B_695, '#skF_1') | v2_struct_0(B_695))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_6868])).
% 10.07/3.87  tff(c_7054, plain, (![B_695]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_695, '#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_695, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_695, '#skF_3')) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(B_695, '#skF_4') | r1_tsep_1(B_695, '#skF_3') | ~m1_pre_topc(B_695, '#skF_1') | v2_struct_0(B_695) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_7039])).
% 10.07/3.87  tff(c_7073, plain, (![B_695]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_695, '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_695, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_695, '#skF_3')) | ~m1_pre_topc(B_695, '#skF_4') | r1_tsep_1(B_695, '#skF_3') | ~m1_pre_topc(B_695, '#skF_1') | v2_struct_0(B_695) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_36, c_40, c_50, c_44, c_7054])).
% 10.07/3.87  tff(c_7075, plain, (![B_697]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', B_697, '#skF_3')) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_697, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_697, '#skF_3')) | ~m1_pre_topc(B_697, '#skF_4') | r1_tsep_1(B_697, '#skF_3') | ~m1_pre_topc(B_697, '#skF_1') | v2_struct_0(B_697))), inference(negUnitSimplification, [status(thm)], [c_52, c_38, c_42, c_7073])).
% 10.07/3.87  tff(c_7087, plain, (![B_697, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_697, '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_2', A_10) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', B_697, '#skF_3'), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_697, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_697, '#skF_3')) | ~m1_pre_topc(B_697, '#skF_4') | r1_tsep_1(B_697, '#skF_3') | ~m1_pre_topc(B_697, '#skF_1') | v2_struct_0(B_697))), inference(resolution, [status(thm)], [c_7075, c_14])).
% 10.07/3.87  tff(c_7810, plain, (![B_734, A_735]: (~m1_pre_topc(k2_tsep_1('#skF_1', B_734, '#skF_3'), '#skF_2') | ~m1_pre_topc('#skF_2', A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_734, '#skF_3'), A_735) | ~l1_pre_topc(A_735) | ~v2_pre_topc(A_735) | v2_struct_0(A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', B_734, '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', B_734, '#skF_3')) | ~m1_pre_topc(B_734, '#skF_4') | r1_tsep_1(B_734, '#skF_3') | ~m1_pre_topc(B_734, '#skF_1') | v2_struct_0(B_734))), inference(negUnitSimplification, [status(thm)], [c_46, c_7087])).
% 10.07/3.87  tff(c_7813, plain, (![A_735]: (~m1_pre_topc('#skF_2', A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_735) | ~l1_pre_topc(A_735) | ~v2_pre_topc(A_735) | v2_struct_0(A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_7810])).
% 10.07/3.87  tff(c_7816, plain, (![A_735]: (~m1_pre_topc('#skF_2', A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_735) | ~l1_pre_topc(A_735) | ~v2_pre_topc(A_735) | v2_struct_0(A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_40, c_6442, c_7813])).
% 10.07/3.87  tff(c_7817, plain, (![A_735]: (~m1_pre_topc('#skF_2', A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_735) | ~l1_pre_topc(A_735) | ~v2_pre_topc(A_735) | v2_struct_0(A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_34, c_7816])).
% 10.07/3.87  tff(c_7820, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_7817])).
% 10.07/3.87  tff(c_7823, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_7820])).
% 10.07/3.87  tff(c_7826, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_7823])).
% 10.07/3.87  tff(c_7828, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_7826])).
% 10.07/3.87  tff(c_7830, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitRight, [status(thm)], [c_7817])).
% 10.07/3.87  tff(c_7829, plain, (![A_735]: (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~m1_pre_topc('#skF_2', A_735) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_735) | ~l1_pre_topc(A_735) | ~v2_pre_topc(A_735) | v2_struct_0(A_735))), inference(splitRight, [status(thm)], [c_7817])).
% 10.07/3.87  tff(c_7845, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_7829])).
% 10.07/3.87  tff(c_7848, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7845, c_10])).
% 10.07/3.87  tff(c_7851, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_40, c_7848])).
% 10.07/3.87  tff(c_7853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_42, c_7851])).
% 10.07/3.87  tff(c_7856, plain, (![A_738]: (~m1_pre_topc('#skF_2', A_738) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), A_738) | ~l1_pre_topc(A_738) | ~v2_pre_topc(A_738) | v2_struct_0(A_738))), inference(splitRight, [status(thm)], [c_7829])).
% 10.07/3.87  tff(c_7859, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7830, c_7856])).
% 10.07/3.87  tff(c_7882, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_7859])).
% 10.07/3.87  tff(c_7884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_7882])).
% 10.07/3.87  tff(c_7885, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_6471])).
% 10.07/3.87  tff(c_7985, plain, (![D_779, C_780, B_781, A_782]: (~r1_tsep_1(D_779, C_780) | r1_tsep_1(B_781, D_779) | ~m1_pre_topc(B_781, C_780) | ~m1_pre_topc(D_779, A_782) | v2_struct_0(D_779) | ~m1_pre_topc(C_780, A_782) | v2_struct_0(C_780) | ~m1_pre_topc(B_781, A_782) | v2_struct_0(B_781) | ~l1_pre_topc(A_782) | ~v2_pre_topc(A_782) | v2_struct_0(A_782))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_7989, plain, (![B_781, A_782]: (r1_tsep_1(B_781, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_781, '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_782) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_782) | v2_struct_0('#skF_2') | ~m1_pre_topc(B_781, A_782) | v2_struct_0(B_781) | ~l1_pre_topc(A_782) | ~v2_pre_topc(A_782) | v2_struct_0(A_782))), inference(resolution, [status(thm)], [c_7885, c_7985])).
% 10.07/3.87  tff(c_7995, plain, (![B_781, A_782]: (r1_tsep_1(B_781, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_781, '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_782) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_782) | ~m1_pre_topc(B_781, A_782) | v2_struct_0(B_781) | ~l1_pre_topc(A_782) | ~v2_pre_topc(A_782) | v2_struct_0(A_782))), inference(negUnitSimplification, [status(thm)], [c_46, c_7989])).
% 10.07/3.87  tff(c_8018, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7995])).
% 10.07/3.87  tff(c_8021, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_8018, c_10])).
% 10.07/3.87  tff(c_8024, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_8021])).
% 10.07/3.87  tff(c_8026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_8024])).
% 10.07/3.87  tff(c_8028, plain, (~v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_7995])).
% 10.07/3.87  tff(c_8007, plain, (![C_787, D_788, B_789, A_790]: (~r1_tsep_1(C_787, D_788) | r1_tsep_1(D_788, B_789) | ~m1_pre_topc(B_789, C_787) | ~m1_pre_topc(D_788, A_790) | v2_struct_0(D_788) | ~m1_pre_topc(C_787, A_790) | v2_struct_0(C_787) | ~m1_pre_topc(B_789, A_790) | v2_struct_0(B_789) | ~l1_pre_topc(A_790) | ~v2_pre_topc(A_790) | v2_struct_0(A_790))), inference(cnfTransformation, [status(thm)], [f_130])).
% 10.07/3.87  tff(c_8011, plain, (![B_789, A_790]: (r1_tsep_1('#skF_2', B_789) | ~m1_pre_topc(B_789, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_790) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_790) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_789, A_790) | v2_struct_0(B_789) | ~l1_pre_topc(A_790) | ~v2_pre_topc(A_790) | v2_struct_0(A_790))), inference(resolution, [status(thm)], [c_7885, c_8007])).
% 10.07/3.87  tff(c_8017, plain, (![B_789, A_790]: (r1_tsep_1('#skF_2', B_789) | ~m1_pre_topc(B_789, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_790) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_790) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc(B_789, A_790) | v2_struct_0(B_789) | ~l1_pre_topc(A_790) | ~v2_pre_topc(A_790) | v2_struct_0(A_790))), inference(negUnitSimplification, [status(thm)], [c_46, c_8011])).
% 10.07/3.87  tff(c_8327, plain, (![B_812, A_813]: (r1_tsep_1('#skF_2', B_812) | ~m1_pre_topc(B_812, k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~m1_pre_topc('#skF_2', A_813) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_813) | ~m1_pre_topc(B_812, A_813) | v2_struct_0(B_812) | ~l1_pre_topc(A_813) | ~v2_pre_topc(A_813) | v2_struct_0(A_813))), inference(negUnitSimplification, [status(thm)], [c_8028, c_8017])).
% 10.07/3.87  tff(c_8330, plain, (![C_51, A_813]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_51)) | ~m1_pre_topc('#skF_2', A_813) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_813) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_51), A_813) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_51)) | ~l1_pre_topc(A_813) | ~v2_pre_topc(A_813) | v2_struct_0(A_813) | ~m1_pre_topc(C_51, '#skF_4') | r1_tsep_1('#skF_3', C_51) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc(C_51, '#skF_1') | v2_struct_0(C_51) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_8327])).
% 10.07/3.87  tff(c_8345, plain, (![C_51, A_813]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_51)) | ~m1_pre_topc('#skF_2', A_813) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_813) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_51), A_813) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_51)) | ~l1_pre_topc(A_813) | ~v2_pre_topc(A_813) | v2_struct_0(A_813) | ~m1_pre_topc(C_51, '#skF_4') | r1_tsep_1('#skF_3', C_51) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_51, '#skF_1') | v2_struct_0(C_51) | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_36, c_8330])).
% 10.07/3.87  tff(c_8540, plain, (![C_824, A_825]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_824)) | ~m1_pre_topc('#skF_2', A_825) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_825) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_824), A_825) | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_824)) | ~l1_pre_topc(A_825) | ~v2_pre_topc(A_825) | v2_struct_0(A_825) | ~m1_pre_topc(C_824, '#skF_4') | r1_tsep_1('#skF_3', C_824) | ~m1_pre_topc(C_824, '#skF_1') | v2_struct_0(C_824))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_8345])).
% 10.07/3.87  tff(c_8555, plain, (![C_824]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_824)) | ~m1_pre_topc('#skF_2', '#skF_1') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_824), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_824)) | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_824, '#skF_4') | r1_tsep_1('#skF_3', C_824) | ~m1_pre_topc(C_824, '#skF_1') | v2_struct_0(C_824) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_8540])).
% 10.07/3.87  tff(c_8574, plain, (![C_824]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_824)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_824), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_824)) | ~m1_pre_topc(C_824, '#skF_4') | r1_tsep_1('#skF_3', C_824) | ~m1_pre_topc(C_824, '#skF_1') | v2_struct_0(C_824) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_50, c_44, c_8555])).
% 10.07/3.87  tff(c_8576, plain, (![C_826]: (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', C_826)) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_826), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_826)) | ~m1_pre_topc(C_826, '#skF_4') | r1_tsep_1('#skF_3', C_826) | ~m1_pre_topc(C_826, '#skF_1') | v2_struct_0(C_826))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_8574])).
% 10.07/3.87  tff(c_8586, plain, (![C_826, A_10]: (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_826), '#skF_2') | ~m1_pre_topc('#skF_2', A_10) | v2_struct_0('#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_826), A_10) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_826), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_826)) | ~m1_pre_topc(C_826, '#skF_4') | r1_tsep_1('#skF_3', C_826) | ~m1_pre_topc(C_826, '#skF_1') | v2_struct_0(C_826))), inference(resolution, [status(thm)], [c_8576, c_14])).
% 10.07/3.87  tff(c_9186, plain, (![C_856, A_857]: (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_856), '#skF_2') | ~m1_pre_topc('#skF_2', A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_856), A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', C_856), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', C_856)) | ~m1_pre_topc(C_856, '#skF_4') | r1_tsep_1('#skF_3', C_856) | ~m1_pre_topc(C_856, '#skF_1') | v2_struct_0(C_856))), inference(negUnitSimplification, [status(thm)], [c_46, c_8586])).
% 10.07/3.87  tff(c_9189, plain, (![A_857]: (~m1_pre_topc('#skF_2', A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_9186])).
% 10.07/3.87  tff(c_9192, plain, (![A_857]: (~m1_pre_topc('#skF_2', A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_44, c_6442, c_9189])).
% 10.07/3.87  tff(c_9193, plain, (![A_857]: (~m1_pre_topc('#skF_2', A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | r1_tsep_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_9192])).
% 10.07/3.87  tff(c_9194, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_9193])).
% 10.07/3.87  tff(c_9197, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_9194])).
% 10.07/3.87  tff(c_9200, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_9197])).
% 10.07/3.87  tff(c_9202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_9200])).
% 10.07/3.87  tff(c_9204, plain, (m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_9193])).
% 10.07/3.87  tff(c_6445, plain, (![B_604, A_605]: (l1_pre_topc(B_604) | ~m1_pre_topc(B_604, A_605) | ~l1_pre_topc(A_605))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.07/3.87  tff(c_6454, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_6445])).
% 10.07/3.87  tff(c_6464, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6454])).
% 10.07/3.87  tff(c_6451, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_6445])).
% 10.07/3.87  tff(c_6461, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6451])).
% 10.07/3.87  tff(c_7899, plain, (![A_745, B_746, C_747]: (m1_pre_topc(k2_tsep_1(A_745, B_746, C_747), A_745) | ~m1_pre_topc(C_747, A_745) | v2_struct_0(C_747) | ~m1_pre_topc(B_746, A_745) | v2_struct_0(B_746) | ~l1_pre_topc(A_745) | v2_struct_0(A_745))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.07/3.87  tff(c_7904, plain, (![A_748, B_749, C_750]: (l1_pre_topc(k2_tsep_1(A_748, B_749, C_750)) | ~m1_pre_topc(C_750, A_748) | v2_struct_0(C_750) | ~m1_pre_topc(B_749, A_748) | v2_struct_0(B_749) | ~l1_pre_topc(A_748) | v2_struct_0(A_748))), inference(resolution, [status(thm)], [c_7899, c_4])).
% 10.07/3.87  tff(c_7889, plain, (r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', '#skF_4')) | ~l1_struct_0('#skF_2') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_7885, c_12])).
% 10.07/3.87  tff(c_7890, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7889])).
% 10.07/3.87  tff(c_7894, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_2, c_7890])).
% 10.07/3.87  tff(c_7907, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_7904, c_7894])).
% 10.07/3.87  tff(c_7910, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_36, c_7907])).
% 10.07/3.87  tff(c_7912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_38, c_7910])).
% 10.07/3.87  tff(c_7913, plain, (~l1_struct_0('#skF_2') | r1_tsep_1('#skF_2', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_7889])).
% 10.07/3.87  tff(c_7916, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_7913])).
% 10.07/3.87  tff(c_7919, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_7916])).
% 10.07/3.87  tff(c_7923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6461, c_7919])).
% 10.07/3.87  tff(c_7925, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_7913])).
% 10.07/3.87  tff(c_9203, plain, (![A_857]: (r1_tsep_1('#skF_3', '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2')) | ~m1_pre_topc('#skF_2', A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857))), inference(splitRight, [status(thm)], [c_9193])).
% 10.07/3.87  tff(c_9219, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_9203])).
% 10.07/3.87  tff(c_9223, plain, (~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_9219, c_10])).
% 10.07/3.87  tff(c_9226, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_44, c_9223])).
% 10.07/3.87  tff(c_9228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_46, c_9226])).
% 10.07/3.87  tff(c_9229, plain, (![A_857]: (r1_tsep_1('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', A_857) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_857) | ~l1_pre_topc(A_857) | ~v2_pre_topc(A_857) | v2_struct_0(A_857))), inference(splitRight, [status(thm)], [c_9203])).
% 10.07/3.87  tff(c_9231, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_9229])).
% 10.07/3.87  tff(c_9245, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_9231, c_12])).
% 10.07/3.87  tff(c_9264, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7925, c_9245])).
% 10.07/3.87  tff(c_9265, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_9264])).
% 10.07/3.87  tff(c_9268, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_9265])).
% 10.07/3.87  tff(c_9272, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6464, c_9268])).
% 10.07/3.87  tff(c_9275, plain, (![A_860]: (~m1_pre_topc('#skF_2', A_860) | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_3', '#skF_2'), A_860) | ~l1_pre_topc(A_860) | ~v2_pre_topc(A_860) | v2_struct_0(A_860))), inference(splitRight, [status(thm)], [c_9229])).
% 10.07/3.87  tff(c_9278, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_9204, c_9275])).
% 10.07/3.87  tff(c_9301, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_9278])).
% 10.07/3.87  tff(c_9303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_9301])).
% 10.07/3.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.07/3.87  
% 10.07/3.87  Inference rules
% 10.07/3.87  ----------------------
% 10.07/3.87  #Ref     : 0
% 10.07/3.87  #Sup     : 1551
% 10.07/3.87  #Fact    : 0
% 10.07/3.87  #Define  : 0
% 10.07/3.87  #Split   : 125
% 10.07/3.87  #Chain   : 0
% 10.07/3.87  #Close   : 0
% 10.07/3.87  
% 10.07/3.87  Ordering : KBO
% 10.07/3.87  
% 10.07/3.87  Simplification rules
% 10.07/3.87  ----------------------
% 10.07/3.87  #Subsume      : 454
% 10.07/3.87  #Demod        : 2075
% 10.07/3.87  #Tautology    : 29
% 10.07/3.87  #SimpNegUnit  : 1314
% 10.07/3.87  #BackRed      : 0
% 10.07/3.87  
% 10.07/3.87  #Partial instantiations: 0
% 10.07/3.87  #Strategies tried      : 1
% 10.07/3.87  
% 10.07/3.87  Timing (in seconds)
% 10.07/3.87  ----------------------
% 10.07/3.88  Preprocessing        : 0.34
% 10.07/3.88  Parsing              : 0.19
% 10.07/3.88  CNF conversion       : 0.03
% 10.07/3.88  Main loop            : 2.65
% 10.07/3.88  Inferencing          : 0.59
% 10.07/3.88  Reduction            : 0.65
% 10.07/3.88  Demodulation         : 0.43
% 10.07/3.88  BG Simplification    : 0.06
% 10.07/3.88  Subsumption          : 1.20
% 10.07/3.88  Abstraction          : 0.10
% 10.07/3.88  MUC search           : 0.00
% 10.07/3.88  Cooper               : 0.00
% 10.07/3.88  Total                : 3.13
% 10.07/3.88  Index Insertion      : 0.00
% 10.07/3.88  Index Deletion       : 0.00
% 10.07/3.88  Index Matching       : 0.00
% 10.07/3.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
