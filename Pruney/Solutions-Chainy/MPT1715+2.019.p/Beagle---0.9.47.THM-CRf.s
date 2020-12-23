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
% DateTime   : Thu Dec  3 10:26:40 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 156 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  264 (1008 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(f_100,negated_conjecture,(
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
                   => ( m1_pre_topc(B,C)
                     => ( ( ~ r1_tsep_1(C,D)
                          & ~ r1_tsep_1(D,C) )
                        | ( r1_tsep_1(B,D)
                          & r1_tsep_1(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

tff(f_62,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_14,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_28,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_16,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_20,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_18,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_168,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_198,plain,(
    ! [D_62,B_63,C_64,A_65] :
      ( r1_tsep_1(D_62,B_63)
      | ~ r1_tsep_1(C_64,D_62)
      | ~ m1_pre_topc(B_63,C_64)
      | ~ m1_pre_topc(D_62,A_65)
      | v2_struct_0(D_62)
      | ~ m1_pre_topc(C_64,A_65)
      | v2_struct_0(C_64)
      | ~ m1_pre_topc(B_63,A_65)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_202,plain,(
    ! [B_63,A_65] :
      ( r1_tsep_1('#skF_4',B_63)
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_65)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_65)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_63,A_65)
      | v2_struct_0(B_63)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_168,c_198])).

tff(c_262,plain,(
    ! [B_72,A_73] :
      ( r1_tsep_1('#skF_4',B_72)
      | ~ m1_pre_topc(B_72,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_73)
      | ~ m1_pre_topc('#skF_3',A_73)
      | ~ m1_pre_topc(B_72,A_73)
      | v2_struct_0(B_72)
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_18,c_202])).

tff(c_264,plain,(
    ! [B_72] :
      ( r1_tsep_1('#skF_4',B_72)
      | ~ m1_pre_topc(B_72,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_72,'#skF_1')
      | v2_struct_0(B_72)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_262])).

tff(c_267,plain,(
    ! [B_72] :
      ( r1_tsep_1('#skF_4',B_72)
      | ~ m1_pre_topc(B_72,'#skF_3')
      | ~ m1_pre_topc(B_72,'#skF_1')
      | v2_struct_0(B_72)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_16,c_264])).

tff(c_269,plain,(
    ! [B_74] :
      ( r1_tsep_1('#skF_4',B_74)
      | ~ m1_pre_topc(B_74,'#skF_3')
      | ~ m1_pre_topc(B_74,'#skF_1')
      | v2_struct_0(B_74) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_267])).

tff(c_34,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_83,plain,(
    ! [B_41,D_42,C_43,A_44] :
      ( r1_tsep_1(B_41,D_42)
      | ~ r1_tsep_1(C_43,D_42)
      | ~ m1_pre_topc(B_41,C_43)
      | ~ m1_pre_topc(D_42,A_44)
      | v2_struct_0(D_42)
      | ~ m1_pre_topc(C_43,A_44)
      | v2_struct_0(C_43)
      | ~ m1_pre_topc(B_41,A_44)
      | v2_struct_0(B_41)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_89,plain,(
    ! [B_41,A_44] :
      ( r1_tsep_1(B_41,'#skF_4')
      | ~ m1_pre_topc(B_41,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_44)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_44)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_41,A_44)
      | v2_struct_0(B_41)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_99,plain,(
    ! [B_45,A_46] :
      ( r1_tsep_1(B_45,'#skF_4')
      | ~ m1_pre_topc(B_45,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_46)
      | ~ m1_pre_topc('#skF_3',A_46)
      | ~ m1_pre_topc(B_45,A_46)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_18,c_89])).

tff(c_101,plain,(
    ! [B_45] :
      ( r1_tsep_1(B_45,'#skF_4')
      | ~ m1_pre_topc(B_45,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_45,'#skF_1')
      | v2_struct_0(B_45)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_104,plain,(
    ! [B_45] :
      ( r1_tsep_1(B_45,'#skF_4')
      | ~ m1_pre_topc(B_45,'#skF_3')
      | ~ m1_pre_topc(B_45,'#skF_1')
      | v2_struct_0(B_45)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_16,c_101])).

tff(c_106,plain,(
    ! [B_47] :
      ( r1_tsep_1(B_47,'#skF_4')
      | ~ m1_pre_topc(B_47,'#skF_3')
      | ~ m1_pre_topc(B_47,'#skF_1')
      | v2_struct_0(B_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_104])).

tff(c_10,plain,
    ( ~ r1_tsep_1('#skF_4','#skF_2')
    | ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_33,plain,(
    ~ r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10])).

tff(c_115,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_33])).

tff(c_127,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14,c_115])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_127])).

tff(c_130,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_132,plain,(
    ! [B_48,D_49,C_50,A_51] :
      ( r1_tsep_1(B_48,D_49)
      | ~ r1_tsep_1(D_49,C_50)
      | ~ m1_pre_topc(B_48,C_50)
      | ~ m1_pre_topc(D_49,A_51)
      | v2_struct_0(D_49)
      | ~ m1_pre_topc(C_50,A_51)
      | v2_struct_0(C_50)
      | ~ m1_pre_topc(B_48,A_51)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_134,plain,(
    ! [B_48,A_51] :
      ( r1_tsep_1(B_48,'#skF_4')
      | ~ m1_pre_topc(B_48,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_51)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_51)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_48,A_51)
      | v2_struct_0(B_48)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_130,c_132])).

tff(c_138,plain,(
    ! [B_52,A_53] :
      ( r1_tsep_1(B_52,'#skF_4')
      | ~ m1_pre_topc(B_52,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_53)
      | ~ m1_pre_topc('#skF_3',A_53)
      | ~ m1_pre_topc(B_52,A_53)
      | v2_struct_0(B_52)
      | ~ l1_pre_topc(A_53)
      | ~ v2_pre_topc(A_53)
      | v2_struct_0(A_53) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_18,c_134])).

tff(c_140,plain,(
    ! [B_52] :
      ( r1_tsep_1(B_52,'#skF_4')
      | ~ m1_pre_topc(B_52,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_52,'#skF_1')
      | v2_struct_0(B_52)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_143,plain,(
    ! [B_52] :
      ( r1_tsep_1(B_52,'#skF_4')
      | ~ m1_pre_topc(B_52,'#skF_3')
      | ~ m1_pre_topc(B_52,'#skF_1')
      | v2_struct_0(B_52)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_16,c_140])).

tff(c_145,plain,(
    ! [B_54] :
      ( r1_tsep_1(B_54,'#skF_4')
      | ~ m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_1')
      | v2_struct_0(B_54) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_143])).

tff(c_153,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_145,c_33])).

tff(c_163,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14,c_153])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_163])).

tff(c_166,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_10])).

tff(c_276,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_269,c_166])).

tff(c_285,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14,c_276])).

tff(c_287,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_285])).

tff(c_288,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_415,plain,(
    ! [D_95,B_96,C_97,A_98] :
      ( r1_tsep_1(D_95,B_96)
      | ~ r1_tsep_1(D_95,C_97)
      | ~ m1_pre_topc(B_96,C_97)
      | ~ m1_pre_topc(D_95,A_98)
      | v2_struct_0(D_95)
      | ~ m1_pre_topc(C_97,A_98)
      | v2_struct_0(C_97)
      | ~ m1_pre_topc(B_96,A_98)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_425,plain,(
    ! [B_96,A_98] :
      ( r1_tsep_1('#skF_4',B_96)
      | ~ m1_pre_topc(B_96,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_98)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_98)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_96,A_98)
      | v2_struct_0(B_96)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_288,c_415])).

tff(c_446,plain,(
    ! [B_99,A_100] :
      ( r1_tsep_1('#skF_4',B_99)
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_100)
      | ~ m1_pre_topc('#skF_3',A_100)
      | ~ m1_pre_topc(B_99,A_100)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_18,c_425])).

tff(c_448,plain,(
    ! [B_99] :
      ( r1_tsep_1('#skF_4',B_99)
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_99,'#skF_1')
      | v2_struct_0(B_99)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_446])).

tff(c_451,plain,(
    ! [B_99] :
      ( r1_tsep_1('#skF_4',B_99)
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc(B_99,'#skF_1')
      | v2_struct_0(B_99)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_16,c_448])).

tff(c_484,plain,(
    ! [B_105] :
      ( r1_tsep_1('#skF_4',B_105)
      | ~ m1_pre_topc(B_105,'#skF_3')
      | ~ m1_pre_topc(B_105,'#skF_1')
      | v2_struct_0(B_105) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_451])).

tff(c_495,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_484,c_166])).

tff(c_510,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_14,c_495])).

tff(c_512,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:36:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.35  
% 2.95/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.35  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > l1_pre_topc > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.35  
% 2.95/1.35  %Foreground sorts:
% 2.95/1.35  
% 2.95/1.35  
% 2.95/1.35  %Background operators:
% 2.95/1.35  
% 2.95/1.35  
% 2.95/1.35  %Foreground operators:
% 2.95/1.35  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.95/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.95/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.35  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.95/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.95/1.35  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.95/1.35  
% 3.06/1.37  tff(f_100, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)) | (r1_tsep_1(B, D) & r1_tsep_1(D, B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_tmap_1)).
% 3.06/1.37  tff(f_62, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (m1_pre_topc(B, C) => ((r1_tsep_1(B, D) & r1_tsep_1(D, B)) | (~r1_tsep_1(C, D) & ~r1_tsep_1(D, C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 3.06/1.37  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_24, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_14, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_32, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_30, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_28, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_16, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_20, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_22, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_18, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_12, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_168, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_12])).
% 3.06/1.37  tff(c_198, plain, (![D_62, B_63, C_64, A_65]: (r1_tsep_1(D_62, B_63) | ~r1_tsep_1(C_64, D_62) | ~m1_pre_topc(B_63, C_64) | ~m1_pre_topc(D_62, A_65) | v2_struct_0(D_62) | ~m1_pre_topc(C_64, A_65) | v2_struct_0(C_64) | ~m1_pre_topc(B_63, A_65) | v2_struct_0(B_63) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.37  tff(c_202, plain, (![B_63, A_65]: (r1_tsep_1('#skF_4', B_63) | ~m1_pre_topc(B_63, '#skF_3') | ~m1_pre_topc('#skF_4', A_65) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_65) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_63, A_65) | v2_struct_0(B_63) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_168, c_198])).
% 3.06/1.37  tff(c_262, plain, (![B_72, A_73]: (r1_tsep_1('#skF_4', B_72) | ~m1_pre_topc(B_72, '#skF_3') | ~m1_pre_topc('#skF_4', A_73) | ~m1_pre_topc('#skF_3', A_73) | ~m1_pre_topc(B_72, A_73) | v2_struct_0(B_72) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(negUnitSimplification, [status(thm)], [c_22, c_18, c_202])).
% 3.06/1.37  tff(c_264, plain, (![B_72]: (r1_tsep_1('#skF_4', B_72) | ~m1_pre_topc(B_72, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_72, '#skF_1') | v2_struct_0(B_72) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_262])).
% 3.06/1.37  tff(c_267, plain, (![B_72]: (r1_tsep_1('#skF_4', B_72) | ~m1_pre_topc(B_72, '#skF_3') | ~m1_pre_topc(B_72, '#skF_1') | v2_struct_0(B_72) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_16, c_264])).
% 3.06/1.37  tff(c_269, plain, (![B_74]: (r1_tsep_1('#skF_4', B_74) | ~m1_pre_topc(B_74, '#skF_3') | ~m1_pre_topc(B_74, '#skF_1') | v2_struct_0(B_74))), inference(negUnitSimplification, [status(thm)], [c_32, c_267])).
% 3.06/1.37  tff(c_34, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_12])).
% 3.06/1.37  tff(c_83, plain, (![B_41, D_42, C_43, A_44]: (r1_tsep_1(B_41, D_42) | ~r1_tsep_1(C_43, D_42) | ~m1_pre_topc(B_41, C_43) | ~m1_pre_topc(D_42, A_44) | v2_struct_0(D_42) | ~m1_pre_topc(C_43, A_44) | v2_struct_0(C_43) | ~m1_pre_topc(B_41, A_44) | v2_struct_0(B_41) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.37  tff(c_89, plain, (![B_41, A_44]: (r1_tsep_1(B_41, '#skF_4') | ~m1_pre_topc(B_41, '#skF_3') | ~m1_pre_topc('#skF_4', A_44) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_44) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_41, A_44) | v2_struct_0(B_41) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44) | v2_struct_0(A_44))), inference(resolution, [status(thm)], [c_34, c_83])).
% 3.06/1.37  tff(c_99, plain, (![B_45, A_46]: (r1_tsep_1(B_45, '#skF_4') | ~m1_pre_topc(B_45, '#skF_3') | ~m1_pre_topc('#skF_4', A_46) | ~m1_pre_topc('#skF_3', A_46) | ~m1_pre_topc(B_45, A_46) | v2_struct_0(B_45) | ~l1_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(negUnitSimplification, [status(thm)], [c_22, c_18, c_89])).
% 3.06/1.37  tff(c_101, plain, (![B_45]: (r1_tsep_1(B_45, '#skF_4') | ~m1_pre_topc(B_45, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_45, '#skF_1') | v2_struct_0(B_45) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_99])).
% 3.06/1.37  tff(c_104, plain, (![B_45]: (r1_tsep_1(B_45, '#skF_4') | ~m1_pre_topc(B_45, '#skF_3') | ~m1_pre_topc(B_45, '#skF_1') | v2_struct_0(B_45) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_16, c_101])).
% 3.06/1.37  tff(c_106, plain, (![B_47]: (r1_tsep_1(B_47, '#skF_4') | ~m1_pre_topc(B_47, '#skF_3') | ~m1_pre_topc(B_47, '#skF_1') | v2_struct_0(B_47))), inference(negUnitSimplification, [status(thm)], [c_32, c_104])).
% 3.06/1.37  tff(c_10, plain, (~r1_tsep_1('#skF_4', '#skF_2') | ~r1_tsep_1('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.06/1.37  tff(c_33, plain, (~r1_tsep_1('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_10])).
% 3.06/1.37  tff(c_115, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_106, c_33])).
% 3.06/1.37  tff(c_127, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14, c_115])).
% 3.06/1.37  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_127])).
% 3.06/1.37  tff(c_130, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_12])).
% 3.06/1.37  tff(c_132, plain, (![B_48, D_49, C_50, A_51]: (r1_tsep_1(B_48, D_49) | ~r1_tsep_1(D_49, C_50) | ~m1_pre_topc(B_48, C_50) | ~m1_pre_topc(D_49, A_51) | v2_struct_0(D_49) | ~m1_pre_topc(C_50, A_51) | v2_struct_0(C_50) | ~m1_pre_topc(B_48, A_51) | v2_struct_0(B_48) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.37  tff(c_134, plain, (![B_48, A_51]: (r1_tsep_1(B_48, '#skF_4') | ~m1_pre_topc(B_48, '#skF_3') | ~m1_pre_topc('#skF_4', A_51) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_51) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_48, A_51) | v2_struct_0(B_48) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_130, c_132])).
% 3.06/1.37  tff(c_138, plain, (![B_52, A_53]: (r1_tsep_1(B_52, '#skF_4') | ~m1_pre_topc(B_52, '#skF_3') | ~m1_pre_topc('#skF_4', A_53) | ~m1_pre_topc('#skF_3', A_53) | ~m1_pre_topc(B_52, A_53) | v2_struct_0(B_52) | ~l1_pre_topc(A_53) | ~v2_pre_topc(A_53) | v2_struct_0(A_53))), inference(negUnitSimplification, [status(thm)], [c_22, c_18, c_134])).
% 3.06/1.37  tff(c_140, plain, (![B_52]: (r1_tsep_1(B_52, '#skF_4') | ~m1_pre_topc(B_52, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_52, '#skF_1') | v2_struct_0(B_52) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_138])).
% 3.06/1.37  tff(c_143, plain, (![B_52]: (r1_tsep_1(B_52, '#skF_4') | ~m1_pre_topc(B_52, '#skF_3') | ~m1_pre_topc(B_52, '#skF_1') | v2_struct_0(B_52) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_16, c_140])).
% 3.06/1.37  tff(c_145, plain, (![B_54]: (r1_tsep_1(B_54, '#skF_4') | ~m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, '#skF_1') | v2_struct_0(B_54))), inference(negUnitSimplification, [status(thm)], [c_32, c_143])).
% 3.06/1.37  tff(c_153, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_145, c_33])).
% 3.06/1.37  tff(c_163, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14, c_153])).
% 3.06/1.37  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_163])).
% 3.06/1.37  tff(c_166, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_10])).
% 3.06/1.37  tff(c_276, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_269, c_166])).
% 3.06/1.37  tff(c_285, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14, c_276])).
% 3.06/1.37  tff(c_287, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_285])).
% 3.06/1.37  tff(c_288, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_12])).
% 3.06/1.37  tff(c_415, plain, (![D_95, B_96, C_97, A_98]: (r1_tsep_1(D_95, B_96) | ~r1_tsep_1(D_95, C_97) | ~m1_pre_topc(B_96, C_97) | ~m1_pre_topc(D_95, A_98) | v2_struct_0(D_95) | ~m1_pre_topc(C_97, A_98) | v2_struct_0(C_97) | ~m1_pre_topc(B_96, A_98) | v2_struct_0(B_96) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.06/1.37  tff(c_425, plain, (![B_96, A_98]: (r1_tsep_1('#skF_4', B_96) | ~m1_pre_topc(B_96, '#skF_3') | ~m1_pre_topc('#skF_4', A_98) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_98) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_96, A_98) | v2_struct_0(B_96) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_288, c_415])).
% 3.06/1.37  tff(c_446, plain, (![B_99, A_100]: (r1_tsep_1('#skF_4', B_99) | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc('#skF_4', A_100) | ~m1_pre_topc('#skF_3', A_100) | ~m1_pre_topc(B_99, A_100) | v2_struct_0(B_99) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(negUnitSimplification, [status(thm)], [c_22, c_18, c_425])).
% 3.06/1.37  tff(c_448, plain, (![B_99]: (r1_tsep_1('#skF_4', B_99) | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_99, '#skF_1') | v2_struct_0(B_99) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_446])).
% 3.06/1.37  tff(c_451, plain, (![B_99]: (r1_tsep_1('#skF_4', B_99) | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc(B_99, '#skF_1') | v2_struct_0(B_99) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_16, c_448])).
% 3.06/1.37  tff(c_484, plain, (![B_105]: (r1_tsep_1('#skF_4', B_105) | ~m1_pre_topc(B_105, '#skF_3') | ~m1_pre_topc(B_105, '#skF_1') | v2_struct_0(B_105))), inference(negUnitSimplification, [status(thm)], [c_32, c_451])).
% 3.06/1.37  tff(c_495, plain, (~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_484, c_166])).
% 3.06/1.37  tff(c_510, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_14, c_495])).
% 3.06/1.37  tff(c_512, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_510])).
% 3.06/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.37  
% 3.06/1.37  Inference rules
% 3.06/1.37  ----------------------
% 3.06/1.37  #Ref     : 0
% 3.06/1.37  #Sup     : 80
% 3.06/1.37  #Fact    : 0
% 3.06/1.37  #Define  : 0
% 3.06/1.37  #Split   : 5
% 3.06/1.37  #Chain   : 0
% 3.06/1.37  #Close   : 0
% 3.06/1.37  
% 3.06/1.37  Ordering : KBO
% 3.06/1.37  
% 3.06/1.37  Simplification rules
% 3.06/1.37  ----------------------
% 3.06/1.37  #Subsume      : 2
% 3.06/1.37  #Demod        : 52
% 3.06/1.37  #Tautology    : 0
% 3.06/1.37  #SimpNegUnit  : 80
% 3.06/1.37  #BackRed      : 0
% 3.06/1.37  
% 3.06/1.37  #Partial instantiations: 0
% 3.06/1.37  #Strategies tried      : 1
% 3.06/1.37  
% 3.06/1.37  Timing (in seconds)
% 3.06/1.37  ----------------------
% 3.06/1.37  Preprocessing        : 0.28
% 3.06/1.37  Parsing              : 0.15
% 3.06/1.37  CNF conversion       : 0.02
% 3.06/1.37  Main loop            : 0.33
% 3.06/1.37  Inferencing          : 0.12
% 3.06/1.37  Reduction            : 0.08
% 3.06/1.37  Demodulation         : 0.05
% 3.06/1.37  BG Simplification    : 0.02
% 3.06/1.37  Subsumption          : 0.09
% 3.06/1.37  Abstraction          : 0.02
% 3.06/1.37  MUC search           : 0.00
% 3.06/1.37  Cooper               : 0.00
% 3.06/1.37  Total                : 0.64
% 3.06/1.37  Index Insertion      : 0.00
% 3.06/1.37  Index Deletion       : 0.00
% 3.06/1.37  Index Matching       : 0.00
% 3.06/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
