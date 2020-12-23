%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1642+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   49 (  75 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 250 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v2_struct_0 > l1_orders_2 > k6_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k6_waybel_0,type,(
    k6_waybel_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v4_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r1_orders_2(A,B,C)
                 => r1_tarski(k6_waybel_0(A,C),k6_waybel_0(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k6_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_waybel_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k6_waybel_0(A,B))
              <=> r1_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

tff(f_74,axiom,(
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

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_28,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k6_waybel_0(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,u1_struct_0(A_55))
      | ~ l1_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_30,C_32,B_31] :
      ( m1_subset_1(A_30,C_32)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_70,plain,(
    ! [A_60,A_61,B_62] :
      ( m1_subset_1(A_60,u1_struct_0(A_61))
      | ~ r2_hidden(A_60,k6_waybel_0(A_61,B_62))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_57,c_16])).

tff(c_84,plain,(
    ! [A_61,B_62,B_2] :
      ( m1_subset_1('#skF_1'(k6_waybel_0(A_61,B_62),B_2),u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61)
      | r1_tarski(k6_waybel_0(A_61,B_62),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_85,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_orders_2(A_63,B_64,C_65)
      | ~ r2_hidden(C_65,k6_waybel_0(A_63,B_64))
      | ~ m1_subset_1(C_65,u1_struct_0(A_63))
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [A_82,B_83,B_84] :
      ( r1_orders_2(A_82,B_83,'#skF_1'(k6_waybel_0(A_82,B_83),B_84))
      | ~ m1_subset_1('#skF_1'(k6_waybel_0(A_82,B_83),B_84),u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | v2_struct_0(A_82)
      | r1_tarski(k6_waybel_0(A_82,B_83),B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_140,plain,(
    ! [A_85,B_86,B_87] :
      ( r1_orders_2(A_85,B_86,'#skF_1'(k6_waybel_0(A_85,B_86),B_87))
      | ~ m1_subset_1(B_86,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85)
      | v2_struct_0(A_85)
      | r1_tarski(k6_waybel_0(A_85,B_86),B_87) ) ),
    inference(resolution,[status(thm)],[c_84,c_136])).

tff(c_14,plain,(
    ! [A_15,B_23,D_29,C_27] :
      ( r1_orders_2(A_15,B_23,D_29)
      | ~ r1_orders_2(A_15,C_27,D_29)
      | ~ r1_orders_2(A_15,B_23,C_27)
      | ~ m1_subset_1(D_29,u1_struct_0(A_15))
      | ~ m1_subset_1(C_27,u1_struct_0(A_15))
      | ~ m1_subset_1(B_23,u1_struct_0(A_15))
      | ~ l1_orders_2(A_15)
      | ~ v4_orders_2(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_163,plain,(
    ! [A_101,B_102,B_103,B_104] :
      ( r1_orders_2(A_101,B_102,'#skF_1'(k6_waybel_0(A_101,B_103),B_104))
      | ~ r1_orders_2(A_101,B_102,B_103)
      | ~ m1_subset_1('#skF_1'(k6_waybel_0(A_101,B_103),B_104),u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ v4_orders_2(A_101)
      | ~ m1_subset_1(B_103,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | v2_struct_0(A_101)
      | r1_tarski(k6_waybel_0(A_101,B_103),B_104) ) ),
    inference(resolution,[status(thm)],[c_140,c_14])).

tff(c_167,plain,(
    ! [A_105,B_106,B_107,B_108] :
      ( r1_orders_2(A_105,B_106,'#skF_1'(k6_waybel_0(A_105,B_107),B_108))
      | ~ r1_orders_2(A_105,B_106,B_107)
      | ~ m1_subset_1(B_106,u1_struct_0(A_105))
      | ~ v4_orders_2(A_105)
      | ~ m1_subset_1(B_107,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | v2_struct_0(A_105)
      | r1_tarski(k6_waybel_0(A_105,B_107),B_108) ) ),
    inference(resolution,[status(thm)],[c_84,c_163])).

tff(c_61,plain,(
    ! [C_57,A_58,B_59] :
      ( r2_hidden(C_57,k6_waybel_0(A_58,B_59))
      | ~ r1_orders_2(A_58,B_59,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_1,A_58,B_59] :
      ( r1_tarski(A_1,k6_waybel_0(A_58,B_59))
      | ~ r1_orders_2(A_58,B_59,'#skF_1'(A_1,k6_waybel_0(A_58,B_59)))
      | ~ m1_subset_1('#skF_1'(A_1,k6_waybel_0(A_58,B_59)),u1_struct_0(A_58))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_orders_2(A_58)
      | v2_struct_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_175,plain,(
    ! [A_109,B_110,B_111] :
      ( ~ m1_subset_1('#skF_1'(k6_waybel_0(A_109,B_110),k6_waybel_0(A_109,B_111)),u1_struct_0(A_109))
      | ~ r1_orders_2(A_109,B_111,B_110)
      | ~ m1_subset_1(B_111,u1_struct_0(A_109))
      | ~ v4_orders_2(A_109)
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | v2_struct_0(A_109)
      | r1_tarski(k6_waybel_0(A_109,B_110),k6_waybel_0(A_109,B_111)) ) ),
    inference(resolution,[status(thm)],[c_167,c_69])).

tff(c_181,plain,(
    ! [A_112,B_113,B_114] :
      ( ~ r1_orders_2(A_112,B_113,B_114)
      | ~ m1_subset_1(B_113,u1_struct_0(A_112))
      | ~ v4_orders_2(A_112)
      | ~ m1_subset_1(B_114,u1_struct_0(A_112))
      | ~ l1_orders_2(A_112)
      | v2_struct_0(A_112)
      | r1_tarski(k6_waybel_0(A_112,B_114),k6_waybel_0(A_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_84,c_175])).

tff(c_18,plain,(
    ~ r1_tarski(k6_waybel_0('#skF_2','#skF_4'),k6_waybel_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_190,plain,
    ( ~ r1_orders_2('#skF_2','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ v4_orders_2('#skF_2')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_181,c_18])).

tff(c_196,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_28,c_24,c_20,c_190])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_196])).

%------------------------------------------------------------------------------
