%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:28 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 253 expanded)
%              Number of leaves         :   43 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  165 ( 630 expanded)
%              Number of equality atoms :   27 ( 152 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_lattice3,type,(
    k3_lattice3: $i > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_lattice3,type,(
    k1_lattice3: $i > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k2_yellow19,type,(
    k2_yellow19: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_yellow19,type,(
    k3_yellow19: ( $i * $i * $i ) > $i )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_133,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_subset_1(B,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
              & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
           => B = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

tff(f_63,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_75,axiom,(
    ! [A] : u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_waybel_7)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v2_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & v13_waybel_0(B,k3_yellow_1(k2_struct_0(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
         => k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))),B,k1_tarski(k1_xboole_0)) = k2_yellow19(A,k3_yellow19(A,k2_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow19)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_subset_1(B,u1_struct_0(k3_yellow_1(A)))
            & v2_waybel_0(B,k3_yellow_1(A))
            & v13_waybel_0(B,k3_yellow_1(A))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A)))) )
         => ! [C] :
              ~ ( r2_hidden(C,B)
                & v1_xboole_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_yellow19)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_54,plain,(
    l1_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_30,plain,(
    ! [A_18] : k9_setfam_1(A_18) = k1_zfmisc_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [A_21] : u1_struct_0(k3_yellow_1(A_21)) = k9_setfam_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_50,plain,(
    v1_subset_1('#skF_5',u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_57,plain,(
    v1_subset_1('#skF_5',k9_setfam_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_62,plain,(
    v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_57])).

tff(c_48,plain,(
    v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_46,plain,(
    v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_44])).

tff(c_63,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_58])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_190,plain,(
    ! [A_68,B_69,C_70] :
      ( k7_subset_1(A_68,B_69,C_70) = k4_xboole_0(B_69,C_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_193,plain,(
    ! [C_70] : k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',C_70) = k4_xboole_0('#skF_5',C_70) ),
    inference(resolution,[status(thm)],[c_63,c_190])).

tff(c_38,plain,(
    ! [A_22,B_24] :
      ( k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_22))),B_24,k1_tarski(k1_xboole_0)) = k2_yellow19(A_22,k3_yellow19(A_22,k2_struct_0(A_22),B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_22)))))
      | ~ v13_waybel_0(B_24,k3_yellow_1(k2_struct_0(A_22)))
      | ~ v2_waybel_0(B_24,k3_yellow_1(k2_struct_0(A_22)))
      | v1_xboole_0(B_24)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    ! [A_22,B_24] :
      ( k7_subset_1(k9_setfam_1(k2_struct_0(A_22)),B_24,k1_tarski(k1_xboole_0)) = k2_yellow19(A_22,k3_yellow19(A_22,k2_struct_0(A_22),B_24))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_22))))
      | ~ v13_waybel_0(B_24,k3_yellow_1(k2_struct_0(A_22)))
      | ~ v2_waybel_0(B_24,k3_yellow_1(k2_struct_0(A_22)))
      | v1_xboole_0(B_24)
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_38])).

tff(c_780,plain,(
    ! [A_122,B_123] :
      ( k7_subset_1(k1_zfmisc_1(k2_struct_0(A_122)),B_123,k1_tarski(k1_xboole_0)) = k2_yellow19(A_122,k3_yellow19(A_122,k2_struct_0(A_122),B_123))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_122))))
      | ~ v13_waybel_0(B_123,k3_yellow_1(k2_struct_0(A_122)))
      | ~ v2_waybel_0(B_123,k3_yellow_1(k2_struct_0(A_122)))
      | v1_xboole_0(B_123)
      | ~ l1_struct_0(A_122)
      | v2_struct_0(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_60])).

tff(c_782,plain,
    ( k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')),'#skF_5',k1_tarski(k1_xboole_0)) = k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5'))
    | ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | v1_xboole_0('#skF_5')
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_780])).

tff(c_785,plain,
    ( k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_46,c_193,c_782])).

tff(c_786,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) = k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_52,c_785])).

tff(c_42,plain,(
    k2_yellow19('#skF_4',k3_yellow19('#skF_4',k2_struct_0('#skF_4'),'#skF_5')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_787,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_786,c_42])).

tff(c_107,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_1'(A_44,B_45),B_45)
      | r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_16,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_132,plain,(
    ! [A_53,A_54] :
      ( '#skF_1'(A_53,k1_tarski(A_54)) = A_54
      | r1_xboole_0(A_53,k1_tarski(A_54)) ) ),
    inference(resolution,[status(thm)],[c_107,c_16])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_139,plain,(
    ! [A_53,A_54] :
      ( k4_xboole_0(A_53,k1_tarski(A_54)) = A_53
      | '#skF_1'(A_53,k1_tarski(A_54)) = A_54 ) ),
    inference(resolution,[status(thm)],[c_132,c_12])).

tff(c_799,plain,(
    '#skF_1'('#skF_5',k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_787])).

tff(c_8,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_812,plain,
    ( r2_hidden(k1_xboole_0,'#skF_5')
    | r1_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_799,c_8])).

tff(c_850,plain,(
    r1_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_812])).

tff(c_855,plain,(
    k4_xboole_0('#skF_5',k1_tarski(k1_xboole_0)) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_850,c_12])).

tff(c_860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_855])).

tff(c_861,plain,(
    r2_hidden(k1_xboole_0,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_812])).

tff(c_40,plain,(
    ! [C_31,B_29,A_25] :
      ( ~ v1_xboole_0(C_31)
      | ~ r2_hidden(C_31,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_25))))
      | ~ v13_waybel_0(B_29,k3_yellow_1(A_25))
      | ~ v2_waybel_0(B_29,k3_yellow_1(A_25))
      | ~ v1_subset_1(B_29,u1_struct_0(k3_yellow_1(A_25)))
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_59,plain,(
    ! [C_31,B_29,A_25] :
      ( ~ v1_xboole_0(C_31)
      | ~ r2_hidden(C_31,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k9_setfam_1(A_25)))
      | ~ v13_waybel_0(B_29,k3_yellow_1(A_25))
      | ~ v2_waybel_0(B_29,k3_yellow_1(A_25))
      | ~ v1_subset_1(B_29,k9_setfam_1(A_25))
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_40])).

tff(c_64,plain,(
    ! [C_31,B_29,A_25] :
      ( ~ v1_xboole_0(C_31)
      | ~ r2_hidden(C_31,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ v13_waybel_0(B_29,k3_yellow_1(A_25))
      | ~ v2_waybel_0(B_29,k3_yellow_1(A_25))
      | ~ v1_subset_1(B_29,k1_zfmisc_1(A_25))
      | v1_xboole_0(B_29)
      | v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_59])).

tff(c_864,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_25))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_25))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_25))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(resolution,[status(thm)],[c_861,c_64])).

tff(c_873,plain,(
    ! [A_25] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_25)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_25))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_25))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_25))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_864])).

tff(c_935,plain,(
    ! [A_127] :
      ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(A_127)))
      | ~ v13_waybel_0('#skF_5',k3_yellow_1(A_127))
      | ~ v2_waybel_0('#skF_5',k3_yellow_1(A_127))
      | ~ v1_subset_1('#skF_5',k1_zfmisc_1(A_127))
      | v1_xboole_0(A_127) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_873])).

tff(c_938,plain,
    ( ~ v13_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v2_waybel_0('#skF_5',k3_yellow_1(k2_struct_0('#skF_4')))
    | ~ v1_subset_1('#skF_5',k1_zfmisc_1(k2_struct_0('#skF_4')))
    | v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_63,c_935])).

tff(c_941,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_48,c_46,c_938])).

tff(c_32,plain,(
    ! [A_19] :
      ( ~ v1_xboole_0(k2_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_944,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_941,c_32])).

tff(c_947,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_944])).

tff(c_949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 20:22:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.46  
% 3.14/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.47  %$ v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k7_subset_1 > k3_yellow19 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_yellow19 > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k3_lattice3 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > k1_lattice3 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.14/1.47  
% 3.14/1.47  %Foreground sorts:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Background operators:
% 3.14/1.47  
% 3.14/1.47  
% 3.14/1.47  %Foreground operators:
% 3.14/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.47  tff(k3_lattice3, type, k3_lattice3: $i > $i).
% 3.14/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.47  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.14/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.47  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 3.14/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.14/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.47  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 3.14/1.47  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.14/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.14/1.47  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 3.14/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.14/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.14/1.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.14/1.47  tff(k1_lattice3, type, k1_lattice3: $i > $i).
% 3.14/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.47  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.14/1.47  tff(k2_yellow19, type, k2_yellow19: ($i * $i) > $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.14/1.47  tff(k3_yellow19, type, k3_yellow19: ($i * $i * $i) > $i).
% 3.14/1.47  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 3.14/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.14/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.14/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.14/1.47  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.14/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.14/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.47  
% 3.14/1.48  tff(f_133, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (B = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow19)).
% 3.14/1.48  tff(f_63, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 3.14/1.48  tff(f_75, axiom, (![A]: (u1_struct_0(k3_yellow_1(A)) = k9_setfam_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_waybel_7)).
% 3.14/1.48  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.14/1.48  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.14/1.48  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v1_xboole_0(B) & v2_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(B, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))), B, k1_tarski(k1_xboole_0)) = k2_yellow19(A, k3_yellow19(A, k2_struct_0(A), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow19)).
% 3.14/1.48  tff(f_44, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.14/1.48  tff(f_57, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.14/1.48  tff(f_50, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.14/1.48  tff(f_113, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (((((~v1_xboole_0(B) & v1_subset_1(B, u1_struct_0(k3_yellow_1(A)))) & v2_waybel_0(B, k3_yellow_1(A))) & v13_waybel_0(B, k3_yellow_1(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A))))) => (![C]: ~(r2_hidden(C, B) & v1_xboole_0(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_yellow19)).
% 3.14/1.48  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_struct_0)).
% 3.14/1.48  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_54, plain, (l1_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_30, plain, (![A_18]: (k9_setfam_1(A_18)=k1_zfmisc_1(A_18))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.14/1.48  tff(c_36, plain, (![A_21]: (u1_struct_0(k3_yellow_1(A_21))=k9_setfam_1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.14/1.48  tff(c_50, plain, (v1_subset_1('#skF_5', u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_57, plain, (v1_subset_1('#skF_5', k9_setfam_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_50])).
% 3.14/1.48  tff(c_62, plain, (v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_57])).
% 3.14/1.48  tff(c_48, plain, (v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_46, plain, (v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_4')))))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k9_setfam_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_44])).
% 3.14/1.48  tff(c_63, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_58])).
% 3.14/1.48  tff(c_52, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.14/1.48  tff(c_190, plain, (![A_68, B_69, C_70]: (k7_subset_1(A_68, B_69, C_70)=k4_xboole_0(B_69, C_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.14/1.48  tff(c_193, plain, (![C_70]: (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', C_70)=k4_xboole_0('#skF_5', C_70))), inference(resolution, [status(thm)], [c_63, c_190])).
% 3.14/1.48  tff(c_38, plain, (![A_22, B_24]: (k7_subset_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_22))), B_24, k1_tarski(k1_xboole_0))=k2_yellow19(A_22, k3_yellow19(A_22, k2_struct_0(A_22), B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_22))))) | ~v13_waybel_0(B_24, k3_yellow_1(k2_struct_0(A_22))) | ~v2_waybel_0(B_24, k3_yellow_1(k2_struct_0(A_22))) | v1_xboole_0(B_24) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.14/1.48  tff(c_60, plain, (![A_22, B_24]: (k7_subset_1(k9_setfam_1(k2_struct_0(A_22)), B_24, k1_tarski(k1_xboole_0))=k2_yellow19(A_22, k3_yellow19(A_22, k2_struct_0(A_22), B_24)) | ~m1_subset_1(B_24, k1_zfmisc_1(k9_setfam_1(k2_struct_0(A_22)))) | ~v13_waybel_0(B_24, k3_yellow_1(k2_struct_0(A_22))) | ~v2_waybel_0(B_24, k3_yellow_1(k2_struct_0(A_22))) | v1_xboole_0(B_24) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_38])).
% 3.14/1.48  tff(c_780, plain, (![A_122, B_123]: (k7_subset_1(k1_zfmisc_1(k2_struct_0(A_122)), B_123, k1_tarski(k1_xboole_0))=k2_yellow19(A_122, k3_yellow19(A_122, k2_struct_0(A_122), B_123)) | ~m1_subset_1(B_123, k1_zfmisc_1(k1_zfmisc_1(k2_struct_0(A_122)))) | ~v13_waybel_0(B_123, k3_yellow_1(k2_struct_0(A_122))) | ~v2_waybel_0(B_123, k3_yellow_1(k2_struct_0(A_122))) | v1_xboole_0(B_123) | ~l1_struct_0(A_122) | v2_struct_0(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_60])).
% 3.14/1.48  tff(c_782, plain, (k7_subset_1(k1_zfmisc_1(k2_struct_0('#skF_4')), '#skF_5', k1_tarski(k1_xboole_0))=k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5')) | ~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | v1_xboole_0('#skF_5') | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_63, c_780])).
% 3.14/1.48  tff(c_785, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0)) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48, c_46, c_193, c_782])).
% 3.14/1.48  tff(c_786, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))=k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_56, c_52, c_785])).
% 3.14/1.48  tff(c_42, plain, (k2_yellow19('#skF_4', k3_yellow19('#skF_4', k2_struct_0('#skF_4'), '#skF_5'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.14/1.48  tff(c_787, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_786, c_42])).
% 3.14/1.48  tff(c_107, plain, (![A_44, B_45]: (r2_hidden('#skF_1'(A_44, B_45), B_45) | r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.48  tff(c_16, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.14/1.48  tff(c_132, plain, (![A_53, A_54]: ('#skF_1'(A_53, k1_tarski(A_54))=A_54 | r1_xboole_0(A_53, k1_tarski(A_54)))), inference(resolution, [status(thm)], [c_107, c_16])).
% 3.14/1.48  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.14/1.48  tff(c_139, plain, (![A_53, A_54]: (k4_xboole_0(A_53, k1_tarski(A_54))=A_53 | '#skF_1'(A_53, k1_tarski(A_54))=A_54)), inference(resolution, [status(thm)], [c_132, c_12])).
% 3.14/1.48  tff(c_799, plain, ('#skF_1'('#skF_5', k1_tarski(k1_xboole_0))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_139, c_787])).
% 3.14/1.48  tff(c_8, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.48  tff(c_812, plain, (r2_hidden(k1_xboole_0, '#skF_5') | r1_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_799, c_8])).
% 3.14/1.48  tff(c_850, plain, (r1_xboole_0('#skF_5', k1_tarski(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_812])).
% 3.14/1.48  tff(c_855, plain, (k4_xboole_0('#skF_5', k1_tarski(k1_xboole_0))='#skF_5'), inference(resolution, [status(thm)], [c_850, c_12])).
% 3.14/1.48  tff(c_860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_855])).
% 3.14/1.48  tff(c_861, plain, (r2_hidden(k1_xboole_0, '#skF_5')), inference(splitRight, [status(thm)], [c_812])).
% 3.14/1.48  tff(c_40, plain, (![C_31, B_29, A_25]: (~v1_xboole_0(C_31) | ~r2_hidden(C_31, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(k3_yellow_1(A_25)))) | ~v13_waybel_0(B_29, k3_yellow_1(A_25)) | ~v2_waybel_0(B_29, k3_yellow_1(A_25)) | ~v1_subset_1(B_29, u1_struct_0(k3_yellow_1(A_25))) | v1_xboole_0(B_29) | v1_xboole_0(A_25))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.14/1.48  tff(c_59, plain, (![C_31, B_29, A_25]: (~v1_xboole_0(C_31) | ~r2_hidden(C_31, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k9_setfam_1(A_25))) | ~v13_waybel_0(B_29, k3_yellow_1(A_25)) | ~v2_waybel_0(B_29, k3_yellow_1(A_25)) | ~v1_subset_1(B_29, k9_setfam_1(A_25)) | v1_xboole_0(B_29) | v1_xboole_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_40])).
% 3.14/1.48  tff(c_64, plain, (![C_31, B_29, A_25]: (~v1_xboole_0(C_31) | ~r2_hidden(C_31, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_25))) | ~v13_waybel_0(B_29, k3_yellow_1(A_25)) | ~v2_waybel_0(B_29, k3_yellow_1(A_25)) | ~v1_subset_1(B_29, k1_zfmisc_1(A_25)) | v1_xboole_0(B_29) | v1_xboole_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_59])).
% 3.14/1.48  tff(c_864, plain, (![A_25]: (~v1_xboole_0(k1_xboole_0) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_25))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_25)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_25)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_25)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(resolution, [status(thm)], [c_861, c_64])).
% 3.14/1.48  tff(c_873, plain, (![A_25]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_25))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_25)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_25)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_25)) | v1_xboole_0('#skF_5') | v1_xboole_0(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_864])).
% 3.14/1.48  tff(c_935, plain, (![A_127]: (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(A_127))) | ~v13_waybel_0('#skF_5', k3_yellow_1(A_127)) | ~v2_waybel_0('#skF_5', k3_yellow_1(A_127)) | ~v1_subset_1('#skF_5', k1_zfmisc_1(A_127)) | v1_xboole_0(A_127))), inference(negUnitSimplification, [status(thm)], [c_52, c_873])).
% 3.14/1.48  tff(c_938, plain, (~v13_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v2_waybel_0('#skF_5', k3_yellow_1(k2_struct_0('#skF_4'))) | ~v1_subset_1('#skF_5', k1_zfmisc_1(k2_struct_0('#skF_4'))) | v1_xboole_0(k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_63, c_935])).
% 3.14/1.48  tff(c_941, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_48, c_46, c_938])).
% 3.14/1.48  tff(c_32, plain, (![A_19]: (~v1_xboole_0(k2_struct_0(A_19)) | ~l1_struct_0(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.14/1.48  tff(c_944, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_941, c_32])).
% 3.14/1.48  tff(c_947, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_944])).
% 3.14/1.48  tff(c_949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_947])).
% 3.14/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.48  
% 3.14/1.48  Inference rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Ref     : 0
% 3.14/1.48  #Sup     : 206
% 3.14/1.48  #Fact    : 0
% 3.14/1.48  #Define  : 0
% 3.14/1.48  #Split   : 1
% 3.14/1.48  #Chain   : 0
% 3.14/1.48  #Close   : 0
% 3.14/1.48  
% 3.14/1.48  Ordering : KBO
% 3.14/1.48  
% 3.14/1.48  Simplification rules
% 3.14/1.48  ----------------------
% 3.14/1.48  #Subsume      : 36
% 3.14/1.48  #Demod        : 54
% 3.14/1.48  #Tautology    : 96
% 3.14/1.48  #SimpNegUnit  : 4
% 3.14/1.48  #BackRed      : 1
% 3.14/1.48  
% 3.14/1.48  #Partial instantiations: 0
% 3.28/1.48  #Strategies tried      : 1
% 3.28/1.48  
% 3.28/1.48  Timing (in seconds)
% 3.28/1.48  ----------------------
% 3.28/1.49  Preprocessing        : 0.34
% 3.28/1.49  Parsing              : 0.18
% 3.28/1.49  CNF conversion       : 0.02
% 3.28/1.49  Main loop            : 0.37
% 3.28/1.49  Inferencing          : 0.13
% 3.28/1.49  Reduction            : 0.11
% 3.28/1.49  Demodulation         : 0.07
% 3.28/1.49  BG Simplification    : 0.02
% 3.28/1.49  Subsumption          : 0.08
% 3.28/1.49  Abstraction          : 0.03
% 3.28/1.49  MUC search           : 0.00
% 3.28/1.49  Cooper               : 0.00
% 3.28/1.49  Total                : 0.74
% 3.28/1.49  Index Insertion      : 0.00
% 3.28/1.49  Index Deletion       : 0.00
% 3.28/1.49  Index Matching       : 0.00
% 3.28/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
