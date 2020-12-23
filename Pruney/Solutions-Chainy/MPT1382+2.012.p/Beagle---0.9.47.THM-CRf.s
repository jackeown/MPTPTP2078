%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:08 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 213 expanded)
%              Number of leaves         :   27 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 846 expanded)
%              Number of equality atoms :    4 (  16 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k1_tops_1(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(c_26,plain,(
    m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_382,plain,(
    ! [B_83,A_84,C_85] :
      ( r2_hidden(B_83,k1_tops_1(A_84,C_85))
      | ~ m1_connsp_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ m1_subset_1(B_83,u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | ~ v2_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_387,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_382])).

tff(c_391,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_387])).

tff(c_392,plain,(
    ! [B_83] :
      ( r2_hidden(B_83,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_83)
      | ~ m1_subset_1(B_83,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_391])).

tff(c_393,plain,(
    ! [B_86] :
      ( r2_hidden(B_86,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_86)
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_391])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_397,plain,(
    ! [B_86] :
      ( ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_connsp_2('#skF_4','#skF_2',B_86)
      | ~ m1_subset_1(B_86,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_393,c_2])).

tff(c_398,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_397])).

tff(c_70,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(k1_tops_1(A_51,B_52),B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(u1_struct_0(A_51)))
      | ~ l1_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_70])).

tff(c_79,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_75])).

tff(c_133,plain,(
    ! [A_61,B_62] :
      ( v3_pre_topc(k1_tops_1(A_61,B_62),A_61)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,
    ( v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_133])).

tff(c_142,plain,(
    v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_138])).

tff(c_56,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_56])).

tff(c_66,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(B_50,C_49)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_48] :
      ( r1_tarski(A_48,u1_struct_0('#skF_2'))
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_64,c_66])).

tff(c_149,plain,(
    ! [A_68,B_69] :
      ( k1_tops_1(A_68,k1_tops_1(A_68,B_69)) = k1_tops_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,
    ( k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_149])).

tff(c_158,plain,(
    k1_tops_1('#skF_2',k1_tops_1('#skF_2','#skF_4')) = k1_tops_1('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_154])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,(
    ! [A_51,A_8] :
      ( r1_tarski(k1_tops_1(A_51,A_8),A_8)
      | ~ l1_pre_topc(A_51)
      | ~ r1_tarski(A_8,u1_struct_0(A_51)) ) ),
    inference(resolution,[status(thm)],[c_10,c_70])).

tff(c_167,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | ~ l1_pre_topc('#skF_2')
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_76])).

tff(c_175,plain,
    ( r1_tarski(k1_tops_1('#skF_2','#skF_4'),k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_167])).

tff(c_177,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_180,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_69,c_177])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_180])).

tff(c_186,plain,(
    r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_548,plain,(
    ! [C_95,A_96,B_97] :
      ( m1_connsp_2(C_95,A_96,B_97)
      | ~ r2_hidden(B_97,k1_tops_1(A_96,C_95))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | ~ v2_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_554,plain,(
    ! [B_97] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_97)
      | ~ r2_hidden(B_97,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_548])).

tff(c_566,plain,(
    ! [B_97] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_97)
      | ~ r2_hidden(B_97,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_554])).

tff(c_567,plain,(
    ! [B_97] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_97)
      | ~ r2_hidden(B_97,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1(B_97,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_566])).

tff(c_666,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_2','#skF_4'),k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_669,plain,(
    ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_666])).

tff(c_673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_669])).

tff(c_702,plain,(
    ! [B_102] :
      ( m1_connsp_2(k1_tops_1('#skF_2','#skF_4'),'#skF_2',B_102)
      | ~ r2_hidden(B_102,k1_tops_1('#skF_2','#skF_4'))
      | ~ m1_subset_1(B_102,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_44,plain,(
    ! [D_45] :
      ( ~ r1_tarski(D_45,'#skF_4')
      | ~ v3_pre_topc(D_45,'#skF_2')
      | ~ m1_connsp_2(D_45,'#skF_2','#skF_3')
      | ~ m1_subset_1(D_45,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v1_xboole_0(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_88,plain,(
    ! [A_55] :
      ( ~ r1_tarski(A_55,'#skF_4')
      | ~ v3_pre_topc(A_55,'#skF_2')
      | ~ m1_connsp_2(A_55,'#skF_2','#skF_3')
      | v1_xboole_0(A_55)
      | ~ r1_tarski(A_55,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_95,plain,(
    ! [A_48] :
      ( ~ v3_pre_topc(A_48,'#skF_2')
      | ~ m1_connsp_2(A_48,'#skF_2','#skF_3')
      | v1_xboole_0(A_48)
      | ~ r1_tarski(A_48,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_69,c_88])).

tff(c_708,plain,
    ( ~ v3_pre_topc(k1_tops_1('#skF_2','#skF_4'),'#skF_2')
    | v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r1_tarski(k1_tops_1('#skF_2','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_702,c_95])).

tff(c_715,plain,
    ( v1_xboole_0(k1_tops_1('#skF_2','#skF_4'))
    | ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_79,c_142,c_708])).

tff(c_716,plain,(
    ~ r2_hidden('#skF_3',k1_tops_1('#skF_2','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_715])).

tff(c_719,plain,
    ( ~ m1_connsp_2('#skF_4','#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_392,c_716])).

tff(c_723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_719])).

tff(c_747,plain,(
    ! [B_106] :
      ( ~ m1_connsp_2('#skF_4','#skF_2',B_106)
      | ~ m1_subset_1(B_106,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_397])).

tff(c_750,plain,(
    ~ m1_connsp_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_747])).

tff(c_754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:14:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.64  
% 3.23/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.64  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.23/1.64  
% 3.23/1.64  %Foreground sorts:
% 3.23/1.64  
% 3.23/1.64  
% 3.23/1.64  %Background operators:
% 3.23/1.64  
% 3.23/1.64  
% 3.23/1.64  %Foreground operators:
% 3.23/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.23/1.64  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.23/1.64  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.23/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.23/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.64  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.23/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.23/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.23/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.64  
% 3.23/1.66  tff(f_123, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 3.23/1.66  tff(f_79, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 3.23/1.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.23/1.66  tff(f_62, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 3.23/1.66  tff(f_49, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k1_tops_1(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_tops_1)).
% 3.23/1.66  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.23/1.66  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.23/1.66  tff(f_55, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 3.23/1.66  tff(c_26, plain, (m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_30, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_36, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_382, plain, (![B_83, A_84, C_85]: (r2_hidden(B_83, k1_tops_1(A_84, C_85)) | ~m1_connsp_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~m1_subset_1(B_83, u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | ~v2_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.66  tff(c_387, plain, (![B_83]: (r2_hidden(B_83, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_382])).
% 3.23/1.66  tff(c_391, plain, (![B_83]: (r2_hidden(B_83, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_387])).
% 3.23/1.66  tff(c_392, plain, (![B_83]: (r2_hidden(B_83, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_83) | ~m1_subset_1(B_83, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_391])).
% 3.23/1.66  tff(c_393, plain, (![B_86]: (r2_hidden(B_86, k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_86) | ~m1_subset_1(B_86, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_391])).
% 3.23/1.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.66  tff(c_397, plain, (![B_86]: (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~m1_connsp_2('#skF_4', '#skF_2', B_86) | ~m1_subset_1(B_86, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_393, c_2])).
% 3.23/1.66  tff(c_398, plain, (~v1_xboole_0(k1_tops_1('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_397])).
% 3.23/1.66  tff(c_70, plain, (![A_51, B_52]: (r1_tarski(k1_tops_1(A_51, B_52), B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(u1_struct_0(A_51))) | ~l1_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.23/1.66  tff(c_75, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_70])).
% 3.23/1.66  tff(c_79, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_75])).
% 3.23/1.66  tff(c_133, plain, (![A_61, B_62]: (v3_pre_topc(k1_tops_1(A_61, B_62), A_61) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.23/1.66  tff(c_138, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_133])).
% 3.23/1.66  tff(c_142, plain, (v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_138])).
% 3.23/1.66  tff(c_56, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.66  tff(c_64, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_56])).
% 3.23/1.66  tff(c_66, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(B_50, C_49) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.23/1.66  tff(c_69, plain, (![A_48]: (r1_tarski(A_48, u1_struct_0('#skF_2')) | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_64, c_66])).
% 3.23/1.66  tff(c_149, plain, (![A_68, B_69]: (k1_tops_1(A_68, k1_tops_1(A_68, B_69))=k1_tops_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.23/1.66  tff(c_154, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_149])).
% 3.23/1.66  tff(c_158, plain, (k1_tops_1('#skF_2', k1_tops_1('#skF_2', '#skF_4'))=k1_tops_1('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_154])).
% 3.23/1.66  tff(c_10, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.23/1.66  tff(c_76, plain, (![A_51, A_8]: (r1_tarski(k1_tops_1(A_51, A_8), A_8) | ~l1_pre_topc(A_51) | ~r1_tarski(A_8, u1_struct_0(A_51)))), inference(resolution, [status(thm)], [c_10, c_70])).
% 3.23/1.66  tff(c_167, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | ~l1_pre_topc('#skF_2') | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_76])).
% 3.23/1.66  tff(c_175, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_167])).
% 3.23/1.66  tff(c_177, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_175])).
% 3.23/1.66  tff(c_180, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_69, c_177])).
% 3.23/1.66  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_180])).
% 3.23/1.66  tff(c_186, plain, (r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_175])).
% 3.23/1.66  tff(c_548, plain, (![C_95, A_96, B_97]: (m1_connsp_2(C_95, A_96, B_97) | ~r2_hidden(B_97, k1_tops_1(A_96, C_95)) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | ~v2_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.23/1.66  tff(c_554, plain, (![B_97]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_97) | ~r2_hidden(B_97, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_158, c_548])).
% 3.23/1.66  tff(c_566, plain, (![B_97]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_97) | ~r2_hidden(B_97, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_554])).
% 3.23/1.66  tff(c_567, plain, (![B_97]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_97) | ~r2_hidden(B_97, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1(B_97, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_36, c_566])).
% 3.23/1.66  tff(c_666, plain, (~m1_subset_1(k1_tops_1('#skF_2', '#skF_4'), k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_567])).
% 3.23/1.66  tff(c_669, plain, (~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_10, c_666])).
% 3.23/1.66  tff(c_673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_669])).
% 3.23/1.66  tff(c_702, plain, (![B_102]: (m1_connsp_2(k1_tops_1('#skF_2', '#skF_4'), '#skF_2', B_102) | ~r2_hidden(B_102, k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1(B_102, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_567])).
% 3.23/1.66  tff(c_44, plain, (![D_45]: (~r1_tarski(D_45, '#skF_4') | ~v3_pre_topc(D_45, '#skF_2') | ~m1_connsp_2(D_45, '#skF_2', '#skF_3') | ~m1_subset_1(D_45, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v1_xboole_0(D_45))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.23/1.66  tff(c_88, plain, (![A_55]: (~r1_tarski(A_55, '#skF_4') | ~v3_pre_topc(A_55, '#skF_2') | ~m1_connsp_2(A_55, '#skF_2', '#skF_3') | v1_xboole_0(A_55) | ~r1_tarski(A_55, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_10, c_44])).
% 3.23/1.66  tff(c_95, plain, (![A_48]: (~v3_pre_topc(A_48, '#skF_2') | ~m1_connsp_2(A_48, '#skF_2', '#skF_3') | v1_xboole_0(A_48) | ~r1_tarski(A_48, '#skF_4'))), inference(resolution, [status(thm)], [c_69, c_88])).
% 3.23/1.66  tff(c_708, plain, (~v3_pre_topc(k1_tops_1('#skF_2', '#skF_4'), '#skF_2') | v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r1_tarski(k1_tops_1('#skF_2', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_702, c_95])).
% 3.23/1.66  tff(c_715, plain, (v1_xboole_0(k1_tops_1('#skF_2', '#skF_4')) | ~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_79, c_142, c_708])).
% 3.23/1.66  tff(c_716, plain, (~r2_hidden('#skF_3', k1_tops_1('#skF_2', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_398, c_715])).
% 3.23/1.66  tff(c_719, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_392, c_716])).
% 3.23/1.66  tff(c_723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_719])).
% 3.23/1.66  tff(c_747, plain, (![B_106]: (~m1_connsp_2('#skF_4', '#skF_2', B_106) | ~m1_subset_1(B_106, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_397])).
% 3.23/1.66  tff(c_750, plain, (~m1_connsp_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_747])).
% 3.23/1.66  tff(c_754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_750])).
% 3.23/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.66  
% 3.23/1.66  Inference rules
% 3.23/1.66  ----------------------
% 3.23/1.66  #Ref     : 0
% 3.23/1.66  #Sup     : 148
% 3.23/1.66  #Fact    : 0
% 3.23/1.66  #Define  : 0
% 3.23/1.66  #Split   : 5
% 3.23/1.66  #Chain   : 0
% 3.23/1.66  #Close   : 0
% 3.23/1.66  
% 3.23/1.66  Ordering : KBO
% 3.23/1.66  
% 3.23/1.66  Simplification rules
% 3.23/1.66  ----------------------
% 3.23/1.66  #Subsume      : 36
% 3.23/1.66  #Demod        : 181
% 3.23/1.66  #Tautology    : 49
% 3.23/1.66  #SimpNegUnit  : 11
% 3.23/1.66  #BackRed      : 0
% 3.23/1.66  
% 3.23/1.66  #Partial instantiations: 0
% 3.23/1.66  #Strategies tried      : 1
% 3.23/1.66  
% 3.23/1.66  Timing (in seconds)
% 3.23/1.66  ----------------------
% 3.23/1.66  Preprocessing        : 0.34
% 3.23/1.66  Parsing              : 0.20
% 3.23/1.66  CNF conversion       : 0.03
% 3.23/1.66  Main loop            : 0.46
% 3.23/1.66  Inferencing          : 0.17
% 3.23/1.66  Reduction            : 0.13
% 3.23/1.66  Demodulation         : 0.09
% 3.23/1.66  BG Simplification    : 0.02
% 3.23/1.66  Subsumption          : 0.10
% 3.23/1.66  Abstraction          : 0.02
% 3.23/1.66  MUC search           : 0.00
% 3.23/1.67  Cooper               : 0.00
% 3.23/1.67  Total                : 0.84
% 3.23/1.67  Index Insertion      : 0.00
% 3.23/1.67  Index Deletion       : 0.00
% 3.23/1.67  Index Matching       : 0.00
% 3.23/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
