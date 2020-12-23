%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:46 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 586 expanded)
%              Number of leaves         :   24 ( 207 expanded)
%              Depth                    :   17
%              Number of atoms          :  477 (3732 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_188,negated_conjecture,(
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
                     => ( ( ~ r1_tsep_1(k2_tsep_1(A,B,C),D)
                         => ( ~ r1_tsep_1(B,D)
                            & ~ r1_tsep_1(C,D) ) )
                        & ( ~ r1_tsep_1(D,k2_tsep_1(A,B,C))
                         => ( ~ r1_tsep_1(D,B)
                            & ~ r1_tsep_1(D,C) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_141,axiom,(
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
                     => ( ( m1_pre_topc(B,C)
                          & m1_pre_topc(D,E) )
                       => ( ( ~ r1_tsep_1(C,E)
                            & ~ r1_tsep_1(k2_tsep_1(A,C,E),k1_tsep_1(A,B,D)) )
                          | ( r1_tsep_1(C,D)
                            & r1_tsep_1(E,B) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tmap_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_struct_0(B) )
     => ( r1_tsep_1(A,B)
       => r1_tsep_1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_670,plain,(
    ! [A_168,B_169,C_170] :
      ( m1_pre_topc(k2_tsep_1(A_168,B_169,C_170),A_168)
      | ~ m1_pre_topc(C_170,A_168)
      | v2_struct_0(C_170)
      | ~ m1_pre_topc(B_169,A_168)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [B_4,A_2] :
      ( l1_pre_topc(B_4)
      | ~ m1_pre_topc(B_4,A_2)
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_675,plain,(
    ! [A_171,B_172,C_173] :
      ( l1_pre_topc(k2_tsep_1(A_171,B_172,C_173))
      | ~ m1_pre_topc(C_173,A_171)
      | v2_struct_0(C_173)
      | ~ m1_pre_topc(B_172,A_171)
      | v2_struct_0(B_172)
      | ~ l1_pre_topc(A_171)
      | v2_struct_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_670,c_4])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_57,plain,(
    ! [B_62,A_63] :
      ( l1_pre_topc(B_62)
      | ~ m1_pre_topc(B_62,A_63)
      | ~ l1_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_69,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_79,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_69])).

tff(c_63,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_73,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_63])).

tff(c_28,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_18,plain,(
    ! [A_11,B_15,C_17] :
      ( m1_pre_topc(k2_tsep_1(A_11,B_15,C_17),B_15)
      | r1_tsep_1(B_15,C_17)
      | ~ m1_pre_topc(C_17,A_11)
      | v2_struct_0(C_17)
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

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

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_14,plain,(
    ! [A_10] :
      ( m1_pre_topc(A_10,A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_48,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_83,plain,(
    r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_212,plain,(
    ! [E_99,C_102,B_103,A_100,D_101] :
      ( ~ r1_tsep_1(C_102,E_99)
      | r1_tsep_1(C_102,D_101)
      | ~ m1_pre_topc(D_101,E_99)
      | ~ m1_pre_topc(B_103,C_102)
      | ~ m1_pre_topc(E_99,A_100)
      | v2_struct_0(E_99)
      | ~ m1_pre_topc(D_101,A_100)
      | v2_struct_0(D_101)
      | ~ m1_pre_topc(C_102,A_100)
      | v2_struct_0(C_102)
      | ~ m1_pre_topc(B_103,A_100)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_220,plain,(
    ! [D_101,B_103,A_100] :
      ( r1_tsep_1('#skF_4',D_101)
      | ~ m1_pre_topc(D_101,'#skF_2')
      | ~ m1_pre_topc(B_103,'#skF_4')
      | ~ m1_pre_topc('#skF_2',A_100)
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(D_101,A_100)
      | v2_struct_0(D_101)
      | ~ m1_pre_topc('#skF_4',A_100)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_103,A_100)
      | v2_struct_0(B_103)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_83,c_212])).

tff(c_233,plain,(
    ! [D_104,B_105,A_106] :
      ( r1_tsep_1('#skF_4',D_104)
      | ~ m1_pre_topc(D_104,'#skF_2')
      | ~ m1_pre_topc(B_105,'#skF_4')
      | ~ m1_pre_topc('#skF_2',A_106)
      | ~ m1_pre_topc(D_104,A_106)
      | v2_struct_0(D_104)
      | ~ m1_pre_topc('#skF_4',A_106)
      | ~ m1_pre_topc(B_105,A_106)
      | v2_struct_0(B_105)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_40,c_220])).

tff(c_245,plain,(
    ! [D_104,A_106] :
      ( r1_tsep_1('#skF_4',D_104)
      | ~ m1_pre_topc(D_104,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_106)
      | ~ m1_pre_topc(D_104,A_106)
      | v2_struct_0(D_104)
      | ~ m1_pre_topc('#skF_4',A_106)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_233])).

tff(c_258,plain,(
    ! [D_104,A_106] :
      ( r1_tsep_1('#skF_4',D_104)
      | ~ m1_pre_topc(D_104,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_106)
      | ~ m1_pre_topc(D_104,A_106)
      | v2_struct_0(D_104)
      | ~ m1_pre_topc('#skF_4',A_106)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106)
      | v2_struct_0(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_245])).

tff(c_260,plain,(
    ! [D_107,A_108] :
      ( r1_tsep_1('#skF_4',D_107)
      | ~ m1_pre_topc(D_107,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_108)
      | ~ m1_pre_topc(D_107,A_108)
      | v2_struct_0(D_107)
      | ~ m1_pre_topc('#skF_4',A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_258])).

tff(c_265,plain,(
    ! [D_107] :
      ( r1_tsep_1('#skF_4',D_107)
      | ~ m1_pre_topc(D_107,'#skF_2')
      | ~ m1_pre_topc(D_107,'#skF_1')
      | v2_struct_0(D_107)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_260])).

tff(c_272,plain,(
    ! [D_107] :
      ( r1_tsep_1('#skF_4',D_107)
      | ~ m1_pre_topc(D_107,'#skF_2')
      | ~ m1_pre_topc(D_107,'#skF_1')
      | v2_struct_0(D_107)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_30,c_265])).

tff(c_274,plain,(
    ! [D_109] :
      ( r1_tsep_1('#skF_4',D_109)
      | ~ m1_pre_topc(D_109,'#skF_2')
      | ~ m1_pre_topc(D_109,'#skF_1')
      | v2_struct_0(D_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_272])).

tff(c_52,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | r1_tsep_1('#skF_2','#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_81,plain,(
    ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_290,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_274,c_81])).

tff(c_314,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_290])).

tff(c_317,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_314])).

tff(c_320,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_317])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_320])).

tff(c_323,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_290])).

tff(c_332,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_335,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_332])).

tff(c_338,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_34,c_335])).

tff(c_340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_28,c_338])).

tff(c_341,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_323])).

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

tff(c_345,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_341,c_10])).

tff(c_348,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_345])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_348])).

tff(c_352,plain,(
    ~ r1_tsep_1('#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_66,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_57])).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66])).

tff(c_16,plain,(
    ! [A_11,B_15,C_17] :
      ( m1_pre_topc(k2_tsep_1(A_11,B_15,C_17),C_17)
      | r1_tsep_1(B_15,C_17)
      | ~ m1_pre_topc(C_17,A_11)
      | v2_struct_0(C_17)
      | ~ m1_pre_topc(B_15,A_11)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_351,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_353,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_401,plain,(
    ! [C_140,A_138,E_137,B_141,D_139] :
      ( ~ r1_tsep_1(C_140,E_137)
      | r1_tsep_1(E_137,B_141)
      | ~ m1_pre_topc(D_139,E_137)
      | ~ m1_pre_topc(B_141,C_140)
      | ~ m1_pre_topc(E_137,A_138)
      | v2_struct_0(E_137)
      | ~ m1_pre_topc(D_139,A_138)
      | v2_struct_0(D_139)
      | ~ m1_pre_topc(C_140,A_138)
      | v2_struct_0(C_140)
      | ~ m1_pre_topc(B_141,A_138)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_405,plain,(
    ! [B_141,D_139,A_138] :
      ( r1_tsep_1('#skF_4',B_141)
      | ~ m1_pre_topc(D_139,'#skF_4')
      | ~ m1_pre_topc(B_141,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_138)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(D_139,A_138)
      | v2_struct_0(D_139)
      | ~ m1_pre_topc('#skF_3',A_138)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(B_141,A_138)
      | v2_struct_0(B_141)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_353,c_401])).

tff(c_412,plain,(
    ! [B_142,D_143,A_144] :
      ( r1_tsep_1('#skF_4',B_142)
      | ~ m1_pre_topc(D_143,'#skF_4')
      | ~ m1_pre_topc(B_142,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_144)
      | ~ m1_pre_topc(D_143,A_144)
      | v2_struct_0(D_143)
      | ~ m1_pre_topc('#skF_3',A_144)
      | ~ m1_pre_topc(B_142,A_144)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_405])).

tff(c_424,plain,(
    ! [B_142,A_144] :
      ( r1_tsep_1('#skF_4',B_142)
      | ~ m1_pre_topc(B_142,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_144)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_144)
      | ~ m1_pre_topc(B_142,A_144)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_412])).

tff(c_437,plain,(
    ! [B_142,A_144] :
      ( r1_tsep_1('#skF_4',B_142)
      | ~ m1_pre_topc(B_142,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_144)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3',A_144)
      | ~ m1_pre_topc(B_142,A_144)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_424])).

tff(c_439,plain,(
    ! [B_145,A_146] :
      ( r1_tsep_1('#skF_4',B_145)
      | ~ m1_pre_topc(B_145,'#skF_3')
      | ~ m1_pre_topc('#skF_4',A_146)
      | ~ m1_pre_topc('#skF_3',A_146)
      | ~ m1_pre_topc(B_145,A_146)
      | v2_struct_0(B_145)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_437])).

tff(c_444,plain,(
    ! [B_145] :
      ( r1_tsep_1('#skF_4',B_145)
      | ~ m1_pre_topc(B_145,'#skF_3')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ m1_pre_topc(B_145,'#skF_1')
      | v2_struct_0(B_145)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_439])).

tff(c_451,plain,(
    ! [B_145] :
      ( r1_tsep_1('#skF_4',B_145)
      | ~ m1_pre_topc(B_145,'#skF_3')
      | ~ m1_pre_topc(B_145,'#skF_1')
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_30,c_444])).

tff(c_453,plain,(
    ! [B_147] :
      ( r1_tsep_1('#skF_4',B_147)
      | ~ m1_pre_topc(B_147,'#skF_3')
      | ~ m1_pre_topc(B_147,'#skF_1')
      | v2_struct_0(B_147) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_451])).

tff(c_471,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_453,c_81])).

tff(c_511,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_541,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_511])).

tff(c_544,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_541])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_544])).

tff(c_547,plain,
    ( ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3')
    | v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_555,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_558,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_555])).

tff(c_561,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_34,c_558])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_28,c_561])).

tff(c_564,plain,(
    v2_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_569,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_564,c_10])).

tff(c_572,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_569])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_572])).

tff(c_576,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_575,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_577,plain,(
    r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_575])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tsep_1(B_9,A_8)
      | ~ r1_tsep_1(A_8,B_9)
      | ~ l1_struct_0(B_9)
      | ~ l1_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_579,plain,
    ( r1_tsep_1('#skF_3','#skF_4')
    | ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_577,c_12])).

tff(c_582,plain,
    ( ~ l1_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_576,c_579])).

tff(c_583,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_582])).

tff(c_586,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_583])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_586])).

tff(c_591,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_582])).

tff(c_595,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_591])).

tff(c_599,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_595])).

tff(c_600,plain,(
    r1_tsep_1('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_575])).

tff(c_603,plain,
    ( r1_tsep_1('#skF_4','#skF_2')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_600,c_12])).

tff(c_606,plain,
    ( ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_352,c_603])).

tff(c_607,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_610,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_607])).

tff(c_614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_610])).

tff(c_615,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_619,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_615])).

tff(c_623,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_619])).

tff(c_625,plain,(
    r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_54,plain,
    ( ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ r1_tsep_1('#skF_4',k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_644,plain,(
    ~ r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_625,c_54])).

tff(c_624,plain,
    ( r1_tsep_1('#skF_2','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_626,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_629,plain,
    ( r1_tsep_1('#skF_4','#skF_3')
    | ~ l1_struct_0('#skF_4')
    | ~ l1_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_626,c_12])).

tff(c_633,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_629])).

tff(c_636,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2,c_633])).

tff(c_640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_636])).

tff(c_641,plain,
    ( ~ l1_struct_0('#skF_4')
    | r1_tsep_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_629])).

tff(c_645,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_648,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_645])).

tff(c_652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_648])).

tff(c_654,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_632,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3'))
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_625,c_12])).

tff(c_662,plain,
    ( r1_tsep_1(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4')
    | ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_654,c_632])).

tff(c_663,plain,(
    ~ l1_struct_0(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_644,c_662])).

tff(c_667,plain,(
    ~ l1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2,c_663])).

tff(c_678,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_675,c_667])).

tff(c_681,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_34,c_678])).

tff(c_683,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_40,c_36,c_681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:45:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.47  
% 3.30/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.47  %$ r1_tsep_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_struct_0 > l1_pre_topc > k2_tsep_1 > k1_tsep_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.30/1.47  
% 3.30/1.47  %Foreground sorts:
% 3.30/1.47  
% 3.30/1.47  
% 3.30/1.47  %Background operators:
% 3.30/1.47  
% 3.30/1.47  
% 3.30/1.47  %Foreground operators:
% 3.30/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.30/1.47  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.30/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.30/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.30/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.30/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.30/1.47  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.30/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.30/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.30/1.47  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 3.30/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.30/1.47  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 3.30/1.47  
% 3.30/1.50  tff(f_188, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(B, C) => ((~r1_tsep_1(k2_tsep_1(A, B, C), D) => (~r1_tsep_1(B, D) & ~r1_tsep_1(C, D))) & (~r1_tsep_1(D, k2_tsep_1(A, B, C)) => (~r1_tsep_1(D, B) & ~r1_tsep_1(D, C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_tmap_1)).
% 3.30/1.50  tff(f_58, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 3.30/1.50  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.30/1.50  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.30/1.50  tff(f_96, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (m1_pre_topc(k2_tsep_1(A, B, C), B) & m1_pre_topc(k2_tsep_1(A, B, C), C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tsep_1)).
% 3.30/1.50  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.30/1.50  tff(f_141, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: ((~v2_struct_0(E) & m1_pre_topc(E, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, E)) => ((~r1_tsep_1(C, E) & ~r1_tsep_1(k2_tsep_1(A, C, E), k1_tsep_1(A, B, D))) | (r1_tsep_1(C, D) & r1_tsep_1(E, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tmap_1)).
% 3.30/1.50  tff(f_66, axiom, (![A, B]: ((l1_struct_0(A) & l1_struct_0(B)) => (r1_tsep_1(A, B) => r1_tsep_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 3.30/1.50  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_670, plain, (![A_168, B_169, C_170]: (m1_pre_topc(k2_tsep_1(A_168, B_169, C_170), A_168) | ~m1_pre_topc(C_170, A_168) | v2_struct_0(C_170) | ~m1_pre_topc(B_169, A_168) | v2_struct_0(B_169) | ~l1_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.30/1.50  tff(c_4, plain, (![B_4, A_2]: (l1_pre_topc(B_4) | ~m1_pre_topc(B_4, A_2) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.30/1.50  tff(c_675, plain, (![A_171, B_172, C_173]: (l1_pre_topc(k2_tsep_1(A_171, B_172, C_173)) | ~m1_pre_topc(C_173, A_171) | v2_struct_0(C_173) | ~m1_pre_topc(B_172, A_171) | v2_struct_0(B_172) | ~l1_pre_topc(A_171) | v2_struct_0(A_171))), inference(resolution, [status(thm)], [c_670, c_4])).
% 3.30/1.50  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.30/1.50  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_57, plain, (![B_62, A_63]: (l1_pre_topc(B_62) | ~m1_pre_topc(B_62, A_63) | ~l1_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.30/1.50  tff(c_69, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_57])).
% 3.30/1.50  tff(c_79, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_69])).
% 3.30/1.50  tff(c_63, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_57])).
% 3.30/1.50  tff(c_73, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_63])).
% 3.30/1.50  tff(c_28, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_18, plain, (![A_11, B_15, C_17]: (m1_pre_topc(k2_tsep_1(A_11, B_15, C_17), B_15) | r1_tsep_1(B_15, C_17) | ~m1_pre_topc(C_17, A_11) | v2_struct_0(C_17) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.50  tff(c_6, plain, (![A_5, B_6, C_7]: (m1_pre_topc(k2_tsep_1(A_5, B_6, C_7), A_5) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~m1_pre_topc(B_6, A_5) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.30/1.50  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_14, plain, (![A_10]: (m1_pre_topc(A_10, A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.30/1.50  tff(c_48, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_83, plain, (r1_tsep_1('#skF_4', '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 3.30/1.50  tff(c_212, plain, (![E_99, C_102, B_103, A_100, D_101]: (~r1_tsep_1(C_102, E_99) | r1_tsep_1(C_102, D_101) | ~m1_pre_topc(D_101, E_99) | ~m1_pre_topc(B_103, C_102) | ~m1_pre_topc(E_99, A_100) | v2_struct_0(E_99) | ~m1_pre_topc(D_101, A_100) | v2_struct_0(D_101) | ~m1_pre_topc(C_102, A_100) | v2_struct_0(C_102) | ~m1_pre_topc(B_103, A_100) | v2_struct_0(B_103) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.30/1.50  tff(c_220, plain, (![D_101, B_103, A_100]: (r1_tsep_1('#skF_4', D_101) | ~m1_pre_topc(D_101, '#skF_2') | ~m1_pre_topc(B_103, '#skF_4') | ~m1_pre_topc('#skF_2', A_100) | v2_struct_0('#skF_2') | ~m1_pre_topc(D_101, A_100) | v2_struct_0(D_101) | ~m1_pre_topc('#skF_4', A_100) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_103, A_100) | v2_struct_0(B_103) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(resolution, [status(thm)], [c_83, c_212])).
% 3.30/1.50  tff(c_233, plain, (![D_104, B_105, A_106]: (r1_tsep_1('#skF_4', D_104) | ~m1_pre_topc(D_104, '#skF_2') | ~m1_pre_topc(B_105, '#skF_4') | ~m1_pre_topc('#skF_2', A_106) | ~m1_pre_topc(D_104, A_106) | v2_struct_0(D_104) | ~m1_pre_topc('#skF_4', A_106) | ~m1_pre_topc(B_105, A_106) | v2_struct_0(B_105) | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(negUnitSimplification, [status(thm)], [c_32, c_40, c_220])).
% 3.30/1.50  tff(c_245, plain, (![D_104, A_106]: (r1_tsep_1('#skF_4', D_104) | ~m1_pre_topc(D_104, '#skF_2') | ~m1_pre_topc('#skF_2', A_106) | ~m1_pre_topc(D_104, A_106) | v2_struct_0(D_104) | ~m1_pre_topc('#skF_4', A_106) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_233])).
% 3.30/1.50  tff(c_258, plain, (![D_104, A_106]: (r1_tsep_1('#skF_4', D_104) | ~m1_pre_topc(D_104, '#skF_2') | ~m1_pre_topc('#skF_2', A_106) | ~m1_pre_topc(D_104, A_106) | v2_struct_0(D_104) | ~m1_pre_topc('#skF_4', A_106) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_106) | ~v2_pre_topc(A_106) | v2_struct_0(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_245])).
% 3.30/1.50  tff(c_260, plain, (![D_107, A_108]: (r1_tsep_1('#skF_4', D_107) | ~m1_pre_topc(D_107, '#skF_2') | ~m1_pre_topc('#skF_2', A_108) | ~m1_pre_topc(D_107, A_108) | v2_struct_0(D_107) | ~m1_pre_topc('#skF_4', A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(negUnitSimplification, [status(thm)], [c_32, c_258])).
% 3.30/1.50  tff(c_265, plain, (![D_107]: (r1_tsep_1('#skF_4', D_107) | ~m1_pre_topc(D_107, '#skF_2') | ~m1_pre_topc(D_107, '#skF_1') | v2_struct_0(D_107) | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_260])).
% 3.30/1.50  tff(c_272, plain, (![D_107]: (r1_tsep_1('#skF_4', D_107) | ~m1_pre_topc(D_107, '#skF_2') | ~m1_pre_topc(D_107, '#skF_1') | v2_struct_0(D_107) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_30, c_265])).
% 3.30/1.50  tff(c_274, plain, (![D_109]: (r1_tsep_1('#skF_4', D_109) | ~m1_pre_topc(D_109, '#skF_2') | ~m1_pre_topc(D_109, '#skF_1') | v2_struct_0(D_109))), inference(negUnitSimplification, [status(thm)], [c_46, c_272])).
% 3.30/1.50  tff(c_52, plain, (r1_tsep_1('#skF_3', '#skF_4') | r1_tsep_1('#skF_2', '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_81, plain, (~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_52])).
% 3.30/1.50  tff(c_290, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_274, c_81])).
% 3.30/1.50  tff(c_314, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_290])).
% 3.30/1.50  tff(c_317, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_314])).
% 3.30/1.50  tff(c_320, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_317])).
% 3.30/1.50  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_320])).
% 3.30/1.50  tff(c_323, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_290])).
% 3.30/1.50  tff(c_332, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_323])).
% 3.30/1.50  tff(c_335, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_332])).
% 3.30/1.50  tff(c_338, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_34, c_335])).
% 3.30/1.50  tff(c_340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_28, c_338])).
% 3.30/1.50  tff(c_341, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_323])).
% 3.30/1.50  tff(c_10, plain, (![A_5, B_6, C_7]: (~v2_struct_0(k2_tsep_1(A_5, B_6, C_7)) | ~m1_pre_topc(C_7, A_5) | v2_struct_0(C_7) | ~m1_pre_topc(B_6, A_5) | v2_struct_0(B_6) | ~l1_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.30/1.50  tff(c_345, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_341, c_10])).
% 3.30/1.50  tff(c_348, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_345])).
% 3.30/1.50  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_348])).
% 3.30/1.50  tff(c_352, plain, (~r1_tsep_1('#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 3.30/1.50  tff(c_66, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_57])).
% 3.30/1.50  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_66])).
% 3.30/1.50  tff(c_16, plain, (![A_11, B_15, C_17]: (m1_pre_topc(k2_tsep_1(A_11, B_15, C_17), C_17) | r1_tsep_1(B_15, C_17) | ~m1_pre_topc(C_17, A_11) | v2_struct_0(C_17) | ~m1_pre_topc(B_15, A_11) | v2_struct_0(B_15) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.30/1.50  tff(c_351, plain, (r1_tsep_1('#skF_4', '#skF_3') | r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.30/1.50  tff(c_353, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_351])).
% 3.30/1.50  tff(c_401, plain, (![C_140, A_138, E_137, B_141, D_139]: (~r1_tsep_1(C_140, E_137) | r1_tsep_1(E_137, B_141) | ~m1_pre_topc(D_139, E_137) | ~m1_pre_topc(B_141, C_140) | ~m1_pre_topc(E_137, A_138) | v2_struct_0(E_137) | ~m1_pre_topc(D_139, A_138) | v2_struct_0(D_139) | ~m1_pre_topc(C_140, A_138) | v2_struct_0(C_140) | ~m1_pre_topc(B_141, A_138) | v2_struct_0(B_141) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.30/1.50  tff(c_405, plain, (![B_141, D_139, A_138]: (r1_tsep_1('#skF_4', B_141) | ~m1_pre_topc(D_139, '#skF_4') | ~m1_pre_topc(B_141, '#skF_3') | ~m1_pre_topc('#skF_4', A_138) | v2_struct_0('#skF_4') | ~m1_pre_topc(D_139, A_138) | v2_struct_0(D_139) | ~m1_pre_topc('#skF_3', A_138) | v2_struct_0('#skF_3') | ~m1_pre_topc(B_141, A_138) | v2_struct_0(B_141) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_353, c_401])).
% 3.30/1.50  tff(c_412, plain, (![B_142, D_143, A_144]: (r1_tsep_1('#skF_4', B_142) | ~m1_pre_topc(D_143, '#skF_4') | ~m1_pre_topc(B_142, '#skF_3') | ~m1_pre_topc('#skF_4', A_144) | ~m1_pre_topc(D_143, A_144) | v2_struct_0(D_143) | ~m1_pre_topc('#skF_3', A_144) | ~m1_pre_topc(B_142, A_144) | v2_struct_0(B_142) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_405])).
% 3.30/1.50  tff(c_424, plain, (![B_142, A_144]: (r1_tsep_1('#skF_4', B_142) | ~m1_pre_topc(B_142, '#skF_3') | ~m1_pre_topc('#skF_4', A_144) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_144) | ~m1_pre_topc(B_142, A_144) | v2_struct_0(B_142) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_412])).
% 3.30/1.50  tff(c_437, plain, (![B_142, A_144]: (r1_tsep_1('#skF_4', B_142) | ~m1_pre_topc(B_142, '#skF_3') | ~m1_pre_topc('#skF_4', A_144) | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', A_144) | ~m1_pre_topc(B_142, A_144) | v2_struct_0(B_142) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_424])).
% 3.30/1.50  tff(c_439, plain, (![B_145, A_146]: (r1_tsep_1('#skF_4', B_145) | ~m1_pre_topc(B_145, '#skF_3') | ~m1_pre_topc('#skF_4', A_146) | ~m1_pre_topc('#skF_3', A_146) | ~m1_pre_topc(B_145, A_146) | v2_struct_0(B_145) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_32, c_437])).
% 3.30/1.50  tff(c_444, plain, (![B_145]: (r1_tsep_1('#skF_4', B_145) | ~m1_pre_topc(B_145, '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(B_145, '#skF_1') | v2_struct_0(B_145) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_439])).
% 3.30/1.50  tff(c_451, plain, (![B_145]: (r1_tsep_1('#skF_4', B_145) | ~m1_pre_topc(B_145, '#skF_3') | ~m1_pre_topc(B_145, '#skF_1') | v2_struct_0(B_145) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_30, c_444])).
% 3.30/1.50  tff(c_453, plain, (![B_147]: (r1_tsep_1('#skF_4', B_147) | ~m1_pre_topc(B_147, '#skF_3') | ~m1_pre_topc(B_147, '#skF_1') | v2_struct_0(B_147))), inference(negUnitSimplification, [status(thm)], [c_46, c_451])).
% 3.30/1.50  tff(c_471, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | ~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_453, c_81])).
% 3.30/1.50  tff(c_511, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_471])).
% 3.30/1.50  tff(c_541, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_6, c_511])).
% 3.30/1.50  tff(c_544, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_541])).
% 3.30/1.50  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_544])).
% 3.30/1.50  tff(c_547, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3') | v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_471])).
% 3.30/1.50  tff(c_555, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_547])).
% 3.30/1.50  tff(c_558, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_16, c_555])).
% 3.30/1.50  tff(c_561, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_34, c_558])).
% 3.30/1.50  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_28, c_561])).
% 3.30/1.50  tff(c_564, plain, (v2_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_547])).
% 3.30/1.50  tff(c_569, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_564, c_10])).
% 3.30/1.50  tff(c_572, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_569])).
% 3.30/1.50  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_572])).
% 3.30/1.50  tff(c_576, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_351])).
% 3.30/1.50  tff(c_575, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_351])).
% 3.30/1.50  tff(c_577, plain, (r1_tsep_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_575])).
% 3.30/1.50  tff(c_12, plain, (![B_9, A_8]: (r1_tsep_1(B_9, A_8) | ~r1_tsep_1(A_8, B_9) | ~l1_struct_0(B_9) | ~l1_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.30/1.50  tff(c_579, plain, (r1_tsep_1('#skF_3', '#skF_4') | ~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_577, c_12])).
% 3.30/1.50  tff(c_582, plain, (~l1_struct_0('#skF_3') | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_576, c_579])).
% 3.30/1.50  tff(c_583, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_582])).
% 3.30/1.50  tff(c_586, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2, c_583])).
% 3.30/1.50  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_586])).
% 3.30/1.50  tff(c_591, plain, (~l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_582])).
% 3.30/1.50  tff(c_595, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_591])).
% 3.30/1.50  tff(c_599, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_595])).
% 3.30/1.50  tff(c_600, plain, (r1_tsep_1('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_575])).
% 3.30/1.50  tff(c_603, plain, (r1_tsep_1('#skF_4', '#skF_2') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_600, c_12])).
% 3.30/1.50  tff(c_606, plain, (~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_352, c_603])).
% 3.30/1.50  tff(c_607, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_606])).
% 3.30/1.50  tff(c_610, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_2, c_607])).
% 3.30/1.50  tff(c_614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_610])).
% 3.30/1.50  tff(c_615, plain, (~l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_606])).
% 3.30/1.50  tff(c_619, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2, c_615])).
% 3.30/1.50  tff(c_623, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_619])).
% 3.30/1.50  tff(c_625, plain, (r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 3.30/1.50  tff(c_54, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~r1_tsep_1('#skF_4', k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 3.30/1.50  tff(c_644, plain, (~r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_625, c_54])).
% 3.30/1.50  tff(c_624, plain, (r1_tsep_1('#skF_2', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_52])).
% 3.30/1.50  tff(c_626, plain, (r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_624])).
% 3.30/1.50  tff(c_629, plain, (r1_tsep_1('#skF_4', '#skF_3') | ~l1_struct_0('#skF_4') | ~l1_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_626, c_12])).
% 3.30/1.50  tff(c_633, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_629])).
% 3.30/1.50  tff(c_636, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2, c_633])).
% 3.30/1.50  tff(c_640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_636])).
% 3.30/1.50  tff(c_641, plain, (~l1_struct_0('#skF_4') | r1_tsep_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_629])).
% 3.30/1.50  tff(c_645, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_641])).
% 3.30/1.50  tff(c_648, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2, c_645])).
% 3.30/1.50  tff(c_652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_648])).
% 3.30/1.50  tff(c_654, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_641])).
% 3.30/1.50  tff(c_632, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3')) | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_625, c_12])).
% 3.30/1.50  tff(c_662, plain, (r1_tsep_1(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4') | ~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_654, c_632])).
% 3.30/1.50  tff(c_663, plain, (~l1_struct_0(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_644, c_662])).
% 3.30/1.50  tff(c_667, plain, (~l1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_663])).
% 3.30/1.50  tff(c_678, plain, (~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_675, c_667])).
% 3.30/1.50  tff(c_681, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_34, c_678])).
% 3.30/1.50  tff(c_683, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_40, c_36, c_681])).
% 3.30/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.50  
% 3.30/1.50  Inference rules
% 3.30/1.50  ----------------------
% 3.30/1.50  #Ref     : 0
% 3.30/1.50  #Sup     : 94
% 3.30/1.50  #Fact    : 0
% 3.30/1.50  #Define  : 0
% 3.30/1.50  #Split   : 20
% 3.30/1.50  #Chain   : 0
% 3.30/1.50  #Close   : 0
% 3.30/1.50  
% 3.30/1.50  Ordering : KBO
% 3.30/1.50  
% 3.30/1.50  Simplification rules
% 3.30/1.50  ----------------------
% 3.30/1.50  #Subsume      : 16
% 3.30/1.50  #Demod        : 79
% 3.30/1.50  #Tautology    : 5
% 3.30/1.50  #SimpNegUnit  : 54
% 3.30/1.50  #BackRed      : 0
% 3.30/1.50  
% 3.30/1.50  #Partial instantiations: 0
% 3.30/1.50  #Strategies tried      : 1
% 3.30/1.50  
% 3.30/1.50  Timing (in seconds)
% 3.30/1.50  ----------------------
% 3.30/1.50  Preprocessing        : 0.31
% 3.30/1.50  Parsing              : 0.17
% 3.30/1.50  CNF conversion       : 0.03
% 3.30/1.50  Main loop            : 0.39
% 3.30/1.50  Inferencing          : 0.14
% 3.30/1.50  Reduction            : 0.10
% 3.30/1.50  Demodulation         : 0.07
% 3.30/1.50  BG Simplification    : 0.02
% 3.30/1.50  Subsumption          : 0.11
% 3.30/1.50  Abstraction          : 0.01
% 3.30/1.50  MUC search           : 0.00
% 3.30/1.50  Cooper               : 0.00
% 3.30/1.50  Total                : 0.75
% 3.30/1.50  Index Insertion      : 0.00
% 3.30/1.50  Index Deletion       : 0.00
% 3.30/1.50  Index Matching       : 0.00
% 3.30/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
