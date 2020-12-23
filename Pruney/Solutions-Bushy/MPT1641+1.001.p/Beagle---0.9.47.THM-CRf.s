%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1641+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:10 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 104 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 349 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > v4_orders_2 > v2_struct_0 > l1_orders_2 > k5_waybel_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k5_waybel_0,type,(
    k5_waybel_0: ( $i * $i ) > $i )).

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
                 => r1_tarski(k5_waybel_0(A,B),k5_waybel_0(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k5_waybel_0(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_waybel_0)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k5_waybel_0(A,B))
              <=> r1_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_waybel_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

tff(c_18,plain,(
    ~ r1_tarski(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_26,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k5_waybel_0(A_55,B_56),k1_zfmisc_1(u1_struct_0(A_55)))
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
      | ~ r2_hidden(A_60,k5_waybel_0(A_61,B_62))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_57,c_16])).

tff(c_84,plain,(
    ! [A_61,B_62,B_2] :
      ( m1_subset_1('#skF_1'(k5_waybel_0(A_61,B_62),B_2),u1_struct_0(A_61))
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61)
      | r1_tarski(k5_waybel_0(A_61,B_62),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_85,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_orders_2(A_63,C_64,B_65)
      | ~ r2_hidden(C_64,k5_waybel_0(A_63,B_65))
      | ~ m1_subset_1(C_64,u1_struct_0(A_63))
      | ~ m1_subset_1(B_65,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_136,plain,(
    ! [A_82,B_83,B_84] :
      ( r1_orders_2(A_82,'#skF_1'(k5_waybel_0(A_82,B_83),B_84),B_83)
      | ~ m1_subset_1('#skF_1'(k5_waybel_0(A_82,B_83),B_84),u1_struct_0(A_82))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_orders_2(A_82)
      | v2_struct_0(A_82)
      | r1_tarski(k5_waybel_0(A_82,B_83),B_84) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_139,plain,(
    ! [A_61,B_62,B_2] :
      ( r1_orders_2(A_61,'#skF_1'(k5_waybel_0(A_61,B_62),B_2),B_62)
      | ~ m1_subset_1(B_62,u1_struct_0(A_61))
      | ~ l1_orders_2(A_61)
      | v2_struct_0(A_61)
      | r1_tarski(k5_waybel_0(A_61,B_62),B_2) ) ),
    inference(resolution,[status(thm)],[c_84,c_136])).

tff(c_28,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_20,plain,(
    r1_orders_2('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_101,plain,(
    ! [A_69,B_70,D_71,C_72] :
      ( r1_orders_2(A_69,B_70,D_71)
      | ~ r1_orders_2(A_69,C_72,D_71)
      | ~ r1_orders_2(A_69,B_70,C_72)
      | ~ m1_subset_1(D_71,u1_struct_0(A_69))
      | ~ m1_subset_1(C_72,u1_struct_0(A_69))
      | ~ m1_subset_1(B_70,u1_struct_0(A_69))
      | ~ l1_orders_2(A_69)
      | ~ v4_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_103,plain,(
    ! [B_70] :
      ( r1_orders_2('#skF_2',B_70,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_70,'#skF_3')
      | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_70,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_101])).

tff(c_107,plain,(
    ! [B_73] :
      ( r1_orders_2('#skF_2',B_73,'#skF_4')
      | ~ r1_orders_2('#skF_2',B_73,'#skF_3')
      | ~ m1_subset_1(B_73,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_24,c_22,c_103])).

tff(c_111,plain,(
    ! [B_62,B_2] :
      ( r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2',B_62),B_2),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2',B_62),B_2),'#skF_3')
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k5_waybel_0('#skF_2',B_62),B_2) ) ),
    inference(resolution,[status(thm)],[c_84,c_107])).

tff(c_120,plain,(
    ! [B_62,B_2] :
      ( r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2',B_62),B_2),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2',B_62),B_2),'#skF_3')
      | ~ m1_subset_1(B_62,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2')
      | r1_tarski(k5_waybel_0('#skF_2',B_62),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_111])).

tff(c_144,plain,(
    ! [B_88,B_89] :
      ( r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2',B_88),B_89),'#skF_4')
      | ~ r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2',B_88),B_89),'#skF_3')
      | ~ m1_subset_1(B_88,u1_struct_0('#skF_2'))
      | r1_tarski(k5_waybel_0('#skF_2',B_88),B_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_120])).

tff(c_148,plain,(
    ! [B_2] :
      ( r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2','#skF_3'),B_2),'#skF_4')
      | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),B_2) ) ),
    inference(resolution,[status(thm)],[c_139,c_144])).

tff(c_151,plain,(
    ! [B_2] :
      ( r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2','#skF_3'),B_2),'#skF_4')
      | v2_struct_0('#skF_2')
      | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_148])).

tff(c_152,plain,(
    ! [B_2] :
      ( r1_orders_2('#skF_2','#skF_1'(k5_waybel_0('#skF_2','#skF_3'),B_2),'#skF_4')
      | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),B_2) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_151])).

tff(c_61,plain,(
    ! [C_57,A_58,B_59] :
      ( r2_hidden(C_57,k5_waybel_0(A_58,B_59))
      | ~ r1_orders_2(A_58,C_57,B_59)
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

tff(c_171,plain,(
    ! [A_97,A_98,B_99] :
      ( r1_tarski(A_97,k5_waybel_0(A_98,B_99))
      | ~ r1_orders_2(A_98,'#skF_1'(A_97,k5_waybel_0(A_98,B_99)),B_99)
      | ~ m1_subset_1('#skF_1'(A_97,k5_waybel_0(A_98,B_99)),u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_174,plain,
    ( ~ m1_subset_1('#skF_1'(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_152,c_171])).

tff(c_180,plain,
    ( ~ m1_subset_1('#skF_1'(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_2')
    | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_174])).

tff(c_181,plain,(
    ~ m1_subset_1('#skF_1'(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_30,c_180])).

tff(c_186,plain,
    ( ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_orders_2('#skF_2')
    | v2_struct_0('#skF_2')
    | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_181])).

tff(c_189,plain,
    ( v2_struct_0('#skF_2')
    | r1_tarski(k5_waybel_0('#skF_2','#skF_3'),k5_waybel_0('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_186])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_30,c_189])).

%------------------------------------------------------------------------------
