%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:22 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 344 expanded)
%              Number of leaves         :   46 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :  181 ( 987 expanded)
%              Number of equality atoms :   13 ( 133 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_71,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
          & ~ v1_xboole_0(B)
          & v3_pre_topc(B,A)
          & v4_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_119,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_pre_topc(A)
      <=> ( r2_hidden(u1_struct_0(A),u1_pre_topc(A))
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
             => ( r1_tarski(B,u1_pre_topc(A))
               => r2_hidden(k5_setfam_1(u1_struct_0(A),B),u1_pre_topc(A)) ) )
          & ! [B] :
              ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
             => ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( r2_hidden(B,u1_pre_topc(A))
                      & r2_hidden(C,u1_pre_topc(A)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(A),B,C),u1_pre_topc(A)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> r2_hidden(B,u1_pre_topc(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

tff(c_78,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_5] : r1_tarski('#skF_9',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_86,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_84,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_67,A_68] :
      ( ~ r1_tarski(B_67,A_68)
      | ~ r2_hidden(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [A_73] :
      ( ~ r1_tarski(A_73,'#skF_1'(A_73))
      | v1_xboole_0(A_73) ) ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_157,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_101,c_152])).

tff(c_18,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_2'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_2'(A_15),A_15)
      | A_15 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18])).

tff(c_66,plain,(
    ! [A_43] :
      ( l1_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_124,plain,(
    ! [A_66] :
      ( u1_struct_0(A_66) = k2_struct_0(A_66)
      | ~ l1_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_169,plain,(
    ! [A_75] :
      ( u1_struct_0(A_75) = k2_struct_0(A_75)
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_66,c_124])).

tff(c_173,plain,(
    u1_struct_0('#skF_7') = k2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_84,c_169])).

tff(c_312,plain,(
    ! [A_109] :
      ( m1_subset_1('#skF_6'(A_109),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_317,plain,
    ( m1_subset_1('#skF_6'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_312])).

tff(c_320,plain,
    ( m1_subset_1('#skF_6'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7')))
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_317])).

tff(c_321,plain,(
    m1_subset_1('#skF_6'('#skF_7'),k1_zfmisc_1(k2_struct_0('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_320])).

tff(c_14,plain,(
    ! [C_12,B_11,A_10] :
      ( ~ v1_xboole_0(C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_339,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(k2_struct_0('#skF_7'))
      | ~ r2_hidden(A_10,'#skF_6'('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_321,c_14])).

tff(c_341,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_176,plain,(
    m1_subset_1('#skF_8',k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_82])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    ! [A_44] :
      ( v4_pre_topc(k2_struct_0(A_44),A_44)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_211,plain,(
    ! [A_82] :
      ( r2_hidden(u1_struct_0(A_82),u1_pre_topc(A_82))
      | ~ v2_pre_topc(A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_220,plain,
    ( r2_hidden(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
    | ~ v2_pre_topc('#skF_7')
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_211])).

tff(c_224,plain,(
    r2_hidden(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_86,c_220])).

tff(c_8,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k2_subset_1(A_7),k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [A_7] : m1_subset_1(A_7,k1_zfmisc_1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_415,plain,(
    ! [B_121,A_122] :
      ( v3_pre_topc(B_121,A_122)
      | ~ r2_hidden(B_121,u1_pre_topc(A_122))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_430,plain,(
    ! [A_123] :
      ( v3_pre_topc(u1_struct_0(A_123),A_123)
      | ~ r2_hidden(u1_struct_0(A_123),u1_pre_topc(A_123))
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_100,c_415])).

tff(c_442,plain,
    ( v3_pre_topc(u1_struct_0('#skF_7'),'#skF_7')
    | ~ r2_hidden(k2_struct_0('#skF_7'),u1_pre_topc('#skF_7'))
    | ~ l1_pre_topc('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_430])).

tff(c_447,plain,(
    v3_pre_topc(k2_struct_0('#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_224,c_173,c_442])).

tff(c_158,plain,(
    ! [D_74] :
      ( v4_pre_topc(D_74,'#skF_7')
      | ~ r2_hidden(D_74,'#skF_9')
      | ~ m1_subset_1(D_74,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_163,plain,
    ( v4_pre_topc(u1_struct_0('#skF_7'),'#skF_7')
    | ~ r2_hidden(u1_struct_0('#skF_7'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_100,c_158])).

tff(c_190,plain,
    ( v4_pre_topc(k2_struct_0('#skF_7'),'#skF_7')
    | ~ r2_hidden(k2_struct_0('#skF_7'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_173,c_163])).

tff(c_191,plain,(
    ~ r2_hidden(k2_struct_0('#skF_7'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_90,plain,(
    ! [D_58] :
      ( r2_hidden(D_58,'#skF_9')
      | ~ r2_hidden('#skF_8',D_58)
      | ~ v4_pre_topc(D_58,'#skF_7')
      | ~ v3_pre_topc(D_58,'#skF_7')
      | ~ m1_subset_1(D_58,k1_zfmisc_1(u1_struct_0('#skF_7'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_294,plain,(
    ! [D_105] :
      ( r2_hidden(D_105,'#skF_9')
      | ~ r2_hidden('#skF_8',D_105)
      | ~ v4_pre_topc(D_105,'#skF_7')
      | ~ v3_pre_topc(D_105,'#skF_7')
      | ~ m1_subset_1(D_105,k1_zfmisc_1(k2_struct_0('#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_90])).

tff(c_298,plain,
    ( r2_hidden(k2_struct_0('#skF_7'),'#skF_9')
    | ~ r2_hidden('#skF_8',k2_struct_0('#skF_7'))
    | ~ v4_pre_topc(k2_struct_0('#skF_7'),'#skF_7')
    | ~ v3_pre_topc(k2_struct_0('#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_100,c_294])).

tff(c_301,plain,
    ( ~ r2_hidden('#skF_8',k2_struct_0('#skF_7'))
    | ~ v4_pre_topc(k2_struct_0('#skF_7'),'#skF_7')
    | ~ v3_pre_topc(k2_struct_0('#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_191,c_298])).

tff(c_523,plain,
    ( ~ r2_hidden('#skF_8',k2_struct_0('#skF_7'))
    | ~ v4_pre_topc(k2_struct_0('#skF_7'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_301])).

tff(c_524,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_523])).

tff(c_527,plain,
    ( ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_524])).

tff(c_531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_527])).

tff(c_532,plain,(
    ~ r2_hidden('#skF_8',k2_struct_0('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_523])).

tff(c_536,plain,
    ( v1_xboole_0(k2_struct_0('#skF_7'))
    | ~ m1_subset_1('#skF_8',k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_12,c_532])).

tff(c_539,plain,(
    v1_xboole_0(k2_struct_0('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_536])).

tff(c_541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_539])).

tff(c_618,plain,(
    ! [A_132] : ~ r2_hidden(A_132,'#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_632,plain,(
    '#skF_6'('#skF_7') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_99,c_618])).

tff(c_74,plain,(
    ! [A_45] :
      ( ~ v1_xboole_0('#skF_6'(A_45))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_649,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_74])).

tff(c_662,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_157,c_649])).

tff(c_664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_662])).

tff(c_666,plain,(
    r2_hidden(k2_struct_0('#skF_7'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_16,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_670,plain,(
    ~ r1_tarski('#skF_9',k2_struct_0('#skF_7')) ),
    inference(resolution,[status(thm)],[c_666,c_16])).

tff(c_677,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_670])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:50:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.42  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k9_subset_1 > k5_setfam_1 > k4_tarski > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_1 > #skF_7 > #skF_9 > #skF_8 > #skF_3 > #skF_6
% 2.86/1.42  
% 2.86/1.42  %Foreground sorts:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Background operators:
% 2.86/1.42  
% 2.86/1.42  
% 2.86/1.42  %Foreground operators:
% 2.86/1.42  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.86/1.42  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.86/1.42  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.86/1.42  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.86/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.86/1.42  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.86/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.86/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.42  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.86/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.86/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.42  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.86/1.42  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.86/1.42  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.86/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.42  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.86/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.42  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.86/1.42  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.86/1.42  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.86/1.42  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.86/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.42  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.86/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.86/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.42  
% 2.86/1.44  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.86/1.44  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.86/1.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.86/1.44  tff(f_55, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.86/1.44  tff(f_71, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.86/1.44  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.86/1.44  tff(f_100, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.86/1.44  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (?[B]: (((m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) & ~v1_xboole_0(B)) & v3_pre_topc(B, A)) & v4_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_tops_1)).
% 2.86/1.44  tff(f_50, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.86/1.44  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.86/1.44  tff(f_119, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_pre_topc)).
% 2.86/1.44  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (v2_pre_topc(A) <=> ((r2_hidden(u1_struct_0(A), u1_pre_topc(A)) & (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (r1_tarski(B, u1_pre_topc(A)) => r2_hidden(k5_setfam_1(u1_struct_0(A), B), u1_pre_topc(A)))))) & (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((r2_hidden(B, u1_pre_topc(A)) & r2_hidden(C, u1_pre_topc(A))) => r2_hidden(k9_subset_1(u1_struct_0(A), B, C), u1_pre_topc(A))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 2.86/1.44  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.86/1.44  tff(f_37, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.86/1.44  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> r2_hidden(B, u1_pre_topc(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 2.86/1.44  tff(c_78, plain, (k1_xboole_0='#skF_9'), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.44  tff(c_101, plain, (![A_5]: (r1_tarski('#skF_9', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6])).
% 2.86/1.44  tff(c_88, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_86, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_84, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.44  tff(c_129, plain, (![B_67, A_68]: (~r1_tarski(B_67, A_68) | ~r2_hidden(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.44  tff(c_152, plain, (![A_73]: (~r1_tarski(A_73, '#skF_1'(A_73)) | v1_xboole_0(A_73))), inference(resolution, [status(thm)], [c_4, c_129])).
% 2.86/1.44  tff(c_157, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_101, c_152])).
% 2.86/1.44  tff(c_18, plain, (![A_15]: (r2_hidden('#skF_2'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.86/1.44  tff(c_99, plain, (![A_15]: (r2_hidden('#skF_2'(A_15), A_15) | A_15='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18])).
% 2.86/1.44  tff(c_66, plain, (![A_43]: (l1_struct_0(A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.86/1.44  tff(c_124, plain, (![A_66]: (u1_struct_0(A_66)=k2_struct_0(A_66) | ~l1_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.86/1.44  tff(c_169, plain, (![A_75]: (u1_struct_0(A_75)=k2_struct_0(A_75) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_66, c_124])).
% 2.86/1.44  tff(c_173, plain, (u1_struct_0('#skF_7')=k2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_84, c_169])).
% 2.86/1.44  tff(c_312, plain, (![A_109]: (m1_subset_1('#skF_6'(A_109), k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.86/1.44  tff(c_317, plain, (m1_subset_1('#skF_6'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_173, c_312])).
% 2.86/1.44  tff(c_320, plain, (m1_subset_1('#skF_6'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7'))) | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_317])).
% 2.86/1.44  tff(c_321, plain, (m1_subset_1('#skF_6'('#skF_7'), k1_zfmisc_1(k2_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_88, c_320])).
% 2.86/1.44  tff(c_14, plain, (![C_12, B_11, A_10]: (~v1_xboole_0(C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.44  tff(c_339, plain, (![A_10]: (~v1_xboole_0(k2_struct_0('#skF_7')) | ~r2_hidden(A_10, '#skF_6'('#skF_7')))), inference(resolution, [status(thm)], [c_321, c_14])).
% 2.86/1.44  tff(c_341, plain, (~v1_xboole_0(k2_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_339])).
% 2.86/1.44  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_176, plain, (m1_subset_1('#skF_8', k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_82])).
% 2.86/1.44  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.44  tff(c_68, plain, (![A_44]: (v4_pre_topc(k2_struct_0(A_44), A_44) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.86/1.44  tff(c_211, plain, (![A_82]: (r2_hidden(u1_struct_0(A_82), u1_pre_topc(A_82)) | ~v2_pre_topc(A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.86/1.44  tff(c_220, plain, (r2_hidden(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | ~v2_pre_topc('#skF_7') | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_173, c_211])).
% 2.86/1.44  tff(c_224, plain, (r2_hidden(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_86, c_220])).
% 2.86/1.44  tff(c_8, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.44  tff(c_10, plain, (![A_7]: (m1_subset_1(k2_subset_1(A_7), k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.44  tff(c_100, plain, (![A_7]: (m1_subset_1(A_7, k1_zfmisc_1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.86/1.44  tff(c_415, plain, (![B_121, A_122]: (v3_pre_topc(B_121, A_122) | ~r2_hidden(B_121, u1_pre_topc(A_122)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.86/1.44  tff(c_430, plain, (![A_123]: (v3_pre_topc(u1_struct_0(A_123), A_123) | ~r2_hidden(u1_struct_0(A_123), u1_pre_topc(A_123)) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_100, c_415])).
% 2.86/1.44  tff(c_442, plain, (v3_pre_topc(u1_struct_0('#skF_7'), '#skF_7') | ~r2_hidden(k2_struct_0('#skF_7'), u1_pre_topc('#skF_7')) | ~l1_pre_topc('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_173, c_430])).
% 2.86/1.44  tff(c_447, plain, (v3_pre_topc(k2_struct_0('#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_224, c_173, c_442])).
% 2.86/1.44  tff(c_158, plain, (![D_74]: (v4_pre_topc(D_74, '#skF_7') | ~r2_hidden(D_74, '#skF_9') | ~m1_subset_1(D_74, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_163, plain, (v4_pre_topc(u1_struct_0('#skF_7'), '#skF_7') | ~r2_hidden(u1_struct_0('#skF_7'), '#skF_9')), inference(resolution, [status(thm)], [c_100, c_158])).
% 2.86/1.44  tff(c_190, plain, (v4_pre_topc(k2_struct_0('#skF_7'), '#skF_7') | ~r2_hidden(k2_struct_0('#skF_7'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_173, c_163])).
% 2.86/1.44  tff(c_191, plain, (~r2_hidden(k2_struct_0('#skF_7'), '#skF_9')), inference(splitLeft, [status(thm)], [c_190])).
% 2.86/1.44  tff(c_90, plain, (![D_58]: (r2_hidden(D_58, '#skF_9') | ~r2_hidden('#skF_8', D_58) | ~v4_pre_topc(D_58, '#skF_7') | ~v3_pre_topc(D_58, '#skF_7') | ~m1_subset_1(D_58, k1_zfmisc_1(u1_struct_0('#skF_7'))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.86/1.44  tff(c_294, plain, (![D_105]: (r2_hidden(D_105, '#skF_9') | ~r2_hidden('#skF_8', D_105) | ~v4_pre_topc(D_105, '#skF_7') | ~v3_pre_topc(D_105, '#skF_7') | ~m1_subset_1(D_105, k1_zfmisc_1(k2_struct_0('#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_90])).
% 2.86/1.44  tff(c_298, plain, (r2_hidden(k2_struct_0('#skF_7'), '#skF_9') | ~r2_hidden('#skF_8', k2_struct_0('#skF_7')) | ~v4_pre_topc(k2_struct_0('#skF_7'), '#skF_7') | ~v3_pre_topc(k2_struct_0('#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_100, c_294])).
% 2.86/1.44  tff(c_301, plain, (~r2_hidden('#skF_8', k2_struct_0('#skF_7')) | ~v4_pre_topc(k2_struct_0('#skF_7'), '#skF_7') | ~v3_pre_topc(k2_struct_0('#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_191, c_298])).
% 2.86/1.44  tff(c_523, plain, (~r2_hidden('#skF_8', k2_struct_0('#skF_7')) | ~v4_pre_topc(k2_struct_0('#skF_7'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_301])).
% 2.86/1.44  tff(c_524, plain, (~v4_pre_topc(k2_struct_0('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_523])).
% 2.86/1.44  tff(c_527, plain, (~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_68, c_524])).
% 2.86/1.44  tff(c_531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_527])).
% 2.86/1.44  tff(c_532, plain, (~r2_hidden('#skF_8', k2_struct_0('#skF_7'))), inference(splitRight, [status(thm)], [c_523])).
% 2.86/1.44  tff(c_536, plain, (v1_xboole_0(k2_struct_0('#skF_7')) | ~m1_subset_1('#skF_8', k2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_12, c_532])).
% 2.86/1.44  tff(c_539, plain, (v1_xboole_0(k2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_536])).
% 2.86/1.44  tff(c_541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_341, c_539])).
% 2.86/1.44  tff(c_618, plain, (![A_132]: (~r2_hidden(A_132, '#skF_6'('#skF_7')))), inference(splitRight, [status(thm)], [c_339])).
% 2.86/1.44  tff(c_632, plain, ('#skF_6'('#skF_7')='#skF_9'), inference(resolution, [status(thm)], [c_99, c_618])).
% 2.86/1.44  tff(c_74, plain, (![A_45]: (~v1_xboole_0('#skF_6'(A_45)) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.86/1.44  tff(c_649, plain, (~v1_xboole_0('#skF_9') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_632, c_74])).
% 2.86/1.44  tff(c_662, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_157, c_649])).
% 2.86/1.44  tff(c_664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_662])).
% 2.86/1.44  tff(c_666, plain, (r2_hidden(k2_struct_0('#skF_7'), '#skF_9')), inference(splitRight, [status(thm)], [c_190])).
% 2.86/1.44  tff(c_16, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.44  tff(c_670, plain, (~r1_tarski('#skF_9', k2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_666, c_16])).
% 2.86/1.44  tff(c_677, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_670])).
% 2.86/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.44  
% 2.86/1.44  Inference rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Ref     : 0
% 2.86/1.44  #Sup     : 110
% 2.86/1.44  #Fact    : 0
% 2.86/1.44  #Define  : 0
% 2.86/1.44  #Split   : 12
% 2.86/1.44  #Chain   : 0
% 2.86/1.44  #Close   : 0
% 2.86/1.44  
% 2.86/1.44  Ordering : KBO
% 2.86/1.44  
% 2.86/1.44  Simplification rules
% 2.86/1.44  ----------------------
% 2.86/1.44  #Subsume      : 13
% 2.86/1.44  #Demod        : 95
% 2.86/1.44  #Tautology    : 31
% 2.86/1.44  #SimpNegUnit  : 10
% 2.86/1.44  #BackRed      : 20
% 2.86/1.44  
% 2.86/1.44  #Partial instantiations: 0
% 2.86/1.44  #Strategies tried      : 1
% 2.86/1.44  
% 2.86/1.44  Timing (in seconds)
% 2.86/1.44  ----------------------
% 3.19/1.44  Preprocessing        : 0.35
% 3.19/1.44  Parsing              : 0.18
% 3.19/1.44  CNF conversion       : 0.03
% 3.19/1.44  Main loop            : 0.32
% 3.19/1.44  Inferencing          : 0.11
% 3.19/1.44  Reduction            : 0.11
% 3.19/1.44  Demodulation         : 0.07
% 3.19/1.44  BG Simplification    : 0.02
% 3.19/1.44  Subsumption          : 0.06
% 3.19/1.44  Abstraction          : 0.01
% 3.19/1.44  MUC search           : 0.00
% 3.19/1.44  Cooper               : 0.00
% 3.19/1.44  Total                : 0.71
% 3.19/1.44  Index Insertion      : 0.00
% 3.19/1.44  Index Deletion       : 0.00
% 3.19/1.44  Index Matching       : 0.00
% 3.19/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
