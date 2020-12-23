%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:29 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 359 expanded)
%              Number of leaves         :   20 ( 128 expanded)
%              Depth                    :   10
%              Number of atoms          :  521 (1713 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r2_hidden(C,k2_pre_topc(A,B))
                <=> ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ~ ( v3_pre_topc(D,A)
                          & r2_hidden(C,D)
                          & r1_xboole_0(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ( ~ v2_struct_0(A)
                  & ! [D] :
                      ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                     => ~ ( v3_pre_topc(D,A)
                          & r2_hidden(C,D)
                          & r1_xboole_0(B,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_pre_topc)).

tff(c_14,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,
    ( r1_xboole_0('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_43,plain,(
    ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_53,plain,(
    ! [B_46,A_47,C_48] :
      ( r1_xboole_0(B_46,'#skF_1'(A_47,B_46,C_48))
      | r2_hidden(C_48,k2_pre_topc(A_47,B_46))
      | v2_struct_0(A_47)
      | ~ m1_subset_1(C_48,u1_struct_0(A_47))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_55,plain,(
    ! [C_48] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_48))
      | r2_hidden(C_48,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_48,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_58,plain,(
    ! [C_48] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_48))
      | r2_hidden(C_48,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_48,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_55])).

tff(c_60,plain,(
    ! [C_49] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_49))
      | r2_hidden(C_49,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_49,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_58])).

tff(c_65,plain,
    ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_43])).

tff(c_71,plain,(
    r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_80,plain,(
    ! [C_54,A_55,B_56] :
      ( r2_hidden(C_54,'#skF_1'(A_55,B_56,C_54))
      | r2_hidden(C_54,k2_pre_topc(A_55,B_56))
      | v2_struct_0(A_55)
      | ~ m1_subset_1(C_54,u1_struct_0(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    ! [C_54] :
      ( r2_hidden(C_54,'#skF_1'('#skF_2','#skF_3',C_54))
      | r2_hidden(C_54,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_80])).

tff(c_85,plain,(
    ! [C_54] :
      ( r2_hidden(C_54,'#skF_1'('#skF_2','#skF_3',C_54))
      | r2_hidden(C_54,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_54,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_82])).

tff(c_105,plain,(
    ! [C_60] :
      ( r2_hidden(C_60,'#skF_1'('#skF_2','#skF_3',C_60))
      | r2_hidden(C_60,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_60,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_85])).

tff(c_110,plain,
    ( r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_105,c_43])).

tff(c_116,plain,(
    r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_72,plain,(
    ! [A_50,B_51,C_52] :
      ( v3_pre_topc('#skF_1'(A_50,B_51,C_52),A_50)
      | r2_hidden(C_52,k2_pre_topc(A_50,B_51))
      | v2_struct_0(A_50)
      | ~ m1_subset_1(C_52,u1_struct_0(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_74,plain,(
    ! [C_52] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_52),'#skF_2')
      | r2_hidden(C_52,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_52,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_72])).

tff(c_77,plain,(
    ! [C_52] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_52),'#skF_2')
      | r2_hidden(C_52,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_52,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_78,plain,(
    ! [C_52] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_52),'#skF_2')
      | r2_hidden(C_52,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_52,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_77])).

tff(c_87,plain,(
    ! [A_57,B_58,C_59] :
      ( m1_subset_1('#skF_1'(A_57,B_58,C_59),k1_zfmisc_1(u1_struct_0(A_57)))
      | r2_hidden(C_59,k2_pre_topc(A_57,B_58))
      | v2_struct_0(A_57)
      | ~ m1_subset_1(C_59,u1_struct_0(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_38,plain,(
    ! [D_41] :
      ( v3_pre_topc('#skF_5','#skF_2')
      | ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [D_41] :
      ( ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_97,plain,(
    ! [B_58,C_59] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_58,C_59))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_58,C_59))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_58,C_59),'#skF_2')
      | r2_hidden(C_59,k2_pre_topc('#skF_2',B_58))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_59,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_87,c_44])).

tff(c_103,plain,(
    ! [B_58,C_59] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_58,C_59))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_58,C_59))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_58,C_59),'#skF_2')
      | r2_hidden(C_59,k2_pre_topc('#skF_2',B_58))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_59,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_97])).

tff(c_121,plain,(
    ! [B_65,C_66] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_65,C_66))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_65,C_66))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_65,C_66),'#skF_2')
      | r2_hidden(C_66,k2_pre_topc('#skF_2',B_65))
      | ~ m1_subset_1(C_66,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_103])).

tff(c_123,plain,(
    ! [C_52] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_52))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_52))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden(C_52,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_52,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_78,c_121])).

tff(c_127,plain,(
    ! [C_67] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_67))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_67))
      | r2_hidden(C_67,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_67,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_123])).

tff(c_129,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_116,c_127])).

tff(c_133,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_71,c_129])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_133])).

tff(c_136,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_173,plain,(
    ! [B_80,A_81,C_82] :
      ( r1_xboole_0(B_80,'#skF_1'(A_81,B_80,C_82))
      | r2_hidden(C_82,k2_pre_topc(A_81,B_80))
      | v2_struct_0(A_81)
      | ~ m1_subset_1(C_82,u1_struct_0(A_81))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_175,plain,(
    ! [C_82] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_82))
      | r2_hidden(C_82,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_82,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_173])).

tff(c_178,plain,(
    ! [C_82] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_82))
      | r2_hidden(C_82,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_82,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_180,plain,(
    ! [C_83] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_83))
      | r2_hidden(C_83,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_83,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_178])).

tff(c_185,plain,
    ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_180,c_43])).

tff(c_191,plain,(
    r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_185])).

tff(c_154,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,'#skF_1'(A_77,B_78,C_76))
      | r2_hidden(C_76,k2_pre_topc(A_77,B_78))
      | v2_struct_0(A_77)
      | ~ m1_subset_1(C_76,u1_struct_0(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_156,plain,(
    ! [C_76] :
      ( r2_hidden(C_76,'#skF_1'('#skF_2','#skF_3',C_76))
      | r2_hidden(C_76,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_76,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_154])).

tff(c_159,plain,(
    ! [C_76] :
      ( r2_hidden(C_76,'#skF_1'('#skF_2','#skF_3',C_76))
      | r2_hidden(C_76,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_76,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_156])).

tff(c_161,plain,(
    ! [C_79] :
      ( r2_hidden(C_79,'#skF_1'('#skF_2','#skF_3',C_79))
      | r2_hidden(C_79,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_79,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_159])).

tff(c_166,plain,
    ( r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_161,c_43])).

tff(c_172,plain,(
    r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_166])).

tff(c_146,plain,(
    ! [A_72,B_73,C_74] :
      ( v3_pre_topc('#skF_1'(A_72,B_73,C_74),A_72)
      | r2_hidden(C_74,k2_pre_topc(A_72,B_73))
      | v2_struct_0(A_72)
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(u1_struct_0(A_72)))
      | ~ l1_pre_topc(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_148,plain,(
    ! [C_74] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_74),'#skF_2')
      | r2_hidden(C_74,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_74,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_146])).

tff(c_151,plain,(
    ! [C_74] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_74),'#skF_2')
      | r2_hidden(C_74,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_74,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_148])).

tff(c_152,plain,(
    ! [C_74] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_74),'#skF_2')
      | r2_hidden(C_74,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_74,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_151])).

tff(c_192,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_1'(A_84,B_85,C_86),k1_zfmisc_1(u1_struct_0(A_84)))
      | r2_hidden(C_86,k2_pre_topc(A_84,B_85))
      | v2_struct_0(A_84)
      | ~ m1_subset_1(C_86,u1_struct_0(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_4','#skF_5')
      | ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_137,plain,(
    ! [D_41] :
      ( ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_202,plain,(
    ! [B_85,C_86] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_85,C_86))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_85,C_86))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_85,C_86),'#skF_2')
      | r2_hidden(C_86,k2_pre_topc('#skF_2',B_85))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_86,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_192,c_137])).

tff(c_208,plain,(
    ! [B_85,C_86] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_85,C_86))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_85,C_86))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_85,C_86),'#skF_2')
      | r2_hidden(C_86,k2_pre_topc('#skF_2',B_85))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_86,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_202])).

tff(c_210,plain,(
    ! [B_87,C_88] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_87,C_88))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_87,C_88))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_87,C_88),'#skF_2')
      | r2_hidden(C_88,k2_pre_topc('#skF_2',B_87))
      | ~ m1_subset_1(C_88,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_208])).

tff(c_212,plain,(
    ! [C_74] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_74))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_74))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden(C_74,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_74,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_152,c_210])).

tff(c_216,plain,(
    ! [C_89] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_89))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_89))
      | r2_hidden(C_89,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_218,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_172,c_216])).

tff(c_222,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_191,c_218])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_222])).

tff(c_225,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_235,plain,(
    ! [B_94,A_95,C_96] :
      ( r1_xboole_0(B_94,'#skF_1'(A_95,B_94,C_96))
      | r2_hidden(C_96,k2_pre_topc(A_95,B_94))
      | v2_struct_0(A_95)
      | ~ m1_subset_1(C_96,u1_struct_0(A_95))
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_237,plain,(
    ! [C_96] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_96))
      | r2_hidden(C_96,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_235])).

tff(c_240,plain,(
    ! [C_96] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_96))
      | r2_hidden(C_96,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_96,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_237])).

tff(c_242,plain,(
    ! [C_97] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_97))
      | r2_hidden(C_97,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_97,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_240])).

tff(c_247,plain,
    ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_242,c_43])).

tff(c_253,plain,(
    r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_247])).

tff(c_262,plain,(
    ! [C_102,A_103,B_104] :
      ( r2_hidden(C_102,'#skF_1'(A_103,B_104,C_102))
      | r2_hidden(C_102,k2_pre_topc(A_103,B_104))
      | v2_struct_0(A_103)
      | ~ m1_subset_1(C_102,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_264,plain,(
    ! [C_102] :
      ( r2_hidden(C_102,'#skF_1'('#skF_2','#skF_3',C_102))
      | r2_hidden(C_102,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_102,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_262])).

tff(c_267,plain,(
    ! [C_102] :
      ( r2_hidden(C_102,'#skF_1'('#skF_2','#skF_3',C_102))
      | r2_hidden(C_102,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_102,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_264])).

tff(c_287,plain,(
    ! [C_108] :
      ( r2_hidden(C_108,'#skF_1'('#skF_2','#skF_3',C_108))
      | r2_hidden(C_108,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_108,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_267])).

tff(c_292,plain,
    ( r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_287,c_43])).

tff(c_298,plain,(
    r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_292])).

tff(c_254,plain,(
    ! [A_98,B_99,C_100] :
      ( v3_pre_topc('#skF_1'(A_98,B_99,C_100),A_98)
      | r2_hidden(C_100,k2_pre_topc(A_98,B_99))
      | v2_struct_0(A_98)
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_256,plain,(
    ! [C_100] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_100),'#skF_2')
      | r2_hidden(C_100,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_254])).

tff(c_259,plain,(
    ! [C_100] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_100),'#skF_2')
      | r2_hidden(C_100,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_256])).

tff(c_260,plain,(
    ! [C_100] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_100),'#skF_2')
      | r2_hidden(C_100,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_259])).

tff(c_269,plain,(
    ! [A_105,B_106,C_107] :
      ( m1_subset_1('#skF_1'(A_105,B_106,C_107),k1_zfmisc_1(u1_struct_0(A_105)))
      | r2_hidden(C_107,k2_pre_topc(A_105,B_106))
      | v2_struct_0(A_105)
      | ~ m1_subset_1(C_107,u1_struct_0(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_34,plain,(
    ! [D_41] :
      ( r1_xboole_0('#skF_3','#skF_5')
      | ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_226,plain,(
    ! [D_41] :
      ( ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_279,plain,(
    ! [B_106,C_107] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_106,C_107))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_106,C_107))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_106,C_107),'#skF_2')
      | r2_hidden(C_107,k2_pre_topc('#skF_2',B_106))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_107,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_269,c_226])).

tff(c_285,plain,(
    ! [B_106,C_107] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_106,C_107))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_106,C_107))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_106,C_107),'#skF_2')
      | r2_hidden(C_107,k2_pre_topc('#skF_2',B_106))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_107,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_279])).

tff(c_303,plain,(
    ! [B_113,C_114] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_113,C_114))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_113,C_114))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_113,C_114),'#skF_2')
      | r2_hidden(C_114,k2_pre_topc('#skF_2',B_113))
      | ~ m1_subset_1(C_114,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_285])).

tff(c_305,plain,(
    ! [C_100] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_100))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_100))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden(C_100,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_100,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_260,c_303])).

tff(c_309,plain,(
    ! [C_115] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_115))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_115))
      | r2_hidden(C_115,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_115,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_311,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_298,c_309])).

tff(c_315,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_253,c_311])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_315])).

tff(c_318,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_336,plain,(
    ! [B_124,A_125,C_126] :
      ( r1_xboole_0(B_124,'#skF_1'(A_125,B_124,C_126))
      | r2_hidden(C_126,k2_pre_topc(A_125,B_124))
      | v2_struct_0(A_125)
      | ~ m1_subset_1(C_126,u1_struct_0(A_125))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_338,plain,(
    ! [C_126] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_126))
      | r2_hidden(C_126,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_126,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_336])).

tff(c_341,plain,(
    ! [C_126] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_126))
      | r2_hidden(C_126,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_126,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_338])).

tff(c_343,plain,(
    ! [C_127] :
      ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_127))
      | r2_hidden(C_127,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_127,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_341])).

tff(c_348,plain,
    ( r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_343,c_43])).

tff(c_354,plain,(
    r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_348])).

tff(c_355,plain,(
    ! [C_128,A_129,B_130] :
      ( r2_hidden(C_128,'#skF_1'(A_129,B_130,C_128))
      | r2_hidden(C_128,k2_pre_topc(A_129,B_130))
      | v2_struct_0(A_129)
      | ~ m1_subset_1(C_128,u1_struct_0(A_129))
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_357,plain,(
    ! [C_128] :
      ( r2_hidden(C_128,'#skF_1'('#skF_2','#skF_3',C_128))
      | r2_hidden(C_128,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_128,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_355])).

tff(c_360,plain,(
    ! [C_128] :
      ( r2_hidden(C_128,'#skF_1'('#skF_2','#skF_3',C_128))
      | r2_hidden(C_128,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_128,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_357])).

tff(c_362,plain,(
    ! [C_131] :
      ( r2_hidden(C_131,'#skF_1'('#skF_2','#skF_3',C_131))
      | r2_hidden(C_131,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_131,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_360])).

tff(c_367,plain,
    ( r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_362,c_43])).

tff(c_373,plain,(
    r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_367])).

tff(c_328,plain,(
    ! [A_120,B_121,C_122] :
      ( v3_pre_topc('#skF_1'(A_120,B_121,C_122),A_120)
      | r2_hidden(C_122,k2_pre_topc(A_120,B_121))
      | v2_struct_0(A_120)
      | ~ m1_subset_1(C_122,u1_struct_0(A_120))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_330,plain,(
    ! [C_122] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_122),'#skF_2')
      | r2_hidden(C_122,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_122,u1_struct_0('#skF_2'))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_328])).

tff(c_333,plain,(
    ! [C_122] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_122),'#skF_2')
      | r2_hidden(C_122,k2_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_122,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_330])).

tff(c_334,plain,(
    ! [C_122] :
      ( v3_pre_topc('#skF_1'('#skF_2','#skF_3',C_122),'#skF_2')
      | r2_hidden(C_122,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_122,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_333])).

tff(c_374,plain,(
    ! [A_132,B_133,C_134] :
      ( m1_subset_1('#skF_1'(A_132,B_133,C_134),k1_zfmisc_1(u1_struct_0(A_132)))
      | r2_hidden(C_134,k2_pre_topc(A_132,B_133))
      | v2_struct_0(A_132)
      | ~ m1_subset_1(C_134,u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [D_41] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_320,plain,(
    ! [D_41] :
      ( ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_384,plain,(
    ! [B_133,C_134] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_133,C_134))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_133,C_134))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_133,C_134),'#skF_2')
      | r2_hidden(C_134,k2_pre_topc('#skF_2',B_133))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_374,c_320])).

tff(c_390,plain,(
    ! [B_133,C_134] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_133,C_134))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_133,C_134))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_133,C_134),'#skF_2')
      | r2_hidden(C_134,k2_pre_topc('#skF_2',B_133))
      | v2_struct_0('#skF_2')
      | ~ m1_subset_1(C_134,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_384])).

tff(c_400,plain,(
    ! [B_141,C_142] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2',B_141,C_142))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2',B_141,C_142))
      | ~ v3_pre_topc('#skF_1'('#skF_2',B_141,C_142),'#skF_2')
      | r2_hidden(C_142,k2_pre_topc('#skF_2',B_141))
      | ~ m1_subset_1(C_142,u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_390])).

tff(c_402,plain,(
    ! [C_122] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_122))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_122))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | r2_hidden(C_122,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_122,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_334,c_400])).

tff(c_406,plain,(
    ! [C_143] :
      ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3',C_143))
      | ~ r2_hidden('#skF_4','#skF_1'('#skF_2','#skF_3',C_143))
      | r2_hidden(C_143,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_143,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_402])).

tff(c_408,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4'))
    | r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_373,c_406])).

tff(c_412,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_354,c_408])).

tff(c_414,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_412])).

tff(c_415,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_42,plain,(
    ! [D_41] :
      ( r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3'))
      | ~ r1_xboole_0('#skF_3',D_41)
      | ~ r2_hidden('#skF_4',D_41)
      | ~ v3_pre_topc(D_41,'#skF_2')
      | ~ m1_subset_1(D_41,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_417,plain,(
    ! [D_144] :
      ( ~ r1_xboole_0('#skF_3',D_144)
      | ~ r2_hidden('#skF_4',D_144)
      | ~ v3_pre_topc(D_144,'#skF_2')
      | ~ m1_subset_1(D_144,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_42])).

tff(c_420,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v3_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_415,c_417])).

tff(c_427,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_225,c_318,c_420])).

tff(c_429,plain,(
    r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_26,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_431,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_26])).

tff(c_28,plain,
    ( v3_pre_topc('#skF_5','#skF_2')
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_433,plain,(
    v3_pre_topc('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_28])).

tff(c_30,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ r2_hidden('#skF_4',k2_pre_topc('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_435,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_30])).

tff(c_428,plain,(
    r1_xboole_0('#skF_3','#skF_5') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_522,plain,(
    ! [B_166,D_167,C_168,A_169] :
      ( ~ r1_xboole_0(B_166,D_167)
      | ~ r2_hidden(C_168,D_167)
      | ~ v3_pre_topc(D_167,A_169)
      | ~ m1_subset_1(D_167,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ r2_hidden(C_168,k2_pre_topc(A_169,B_166))
      | ~ m1_subset_1(C_168,u1_struct_0(A_169))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_169)))
      | ~ l1_pre_topc(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_526,plain,(
    ! [C_170,A_171] :
      ( ~ r2_hidden(C_170,'#skF_5')
      | ~ v3_pre_topc('#skF_5',A_171)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ r2_hidden(C_170,k2_pre_topc(A_171,'#skF_3'))
      | ~ m1_subset_1(C_170,u1_struct_0(A_171))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_171)))
      | ~ l1_pre_topc(A_171) ) ),
    inference(resolution,[status(thm)],[c_428,c_522])).

tff(c_528,plain,(
    ! [C_170] :
      ( ~ r2_hidden(C_170,'#skF_5')
      | ~ v3_pre_topc('#skF_5','#skF_2')
      | ~ r2_hidden(C_170,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_170,u1_struct_0('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_435,c_526])).

tff(c_532,plain,(
    ! [C_172] :
      ( ~ r2_hidden(C_172,'#skF_5')
      | ~ r2_hidden(C_172,k2_pre_topc('#skF_2','#skF_3'))
      | ~ m1_subset_1(C_172,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_433,c_528])).

tff(c_541,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_429,c_532])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_431,c_541])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  %$ v3_pre_topc > r2_hidden > r1_xboole_0 > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 2.84/1.40  
% 2.84/1.40  %Foreground sorts:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Background operators:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Foreground operators:
% 2.84/1.40  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.84/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.84/1.40  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.84/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.84/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.84/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.84/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.84/1.40  
% 2.84/1.43  tff(f_74, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_tops_1)).
% 2.84/1.43  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (~v2_struct_0(A) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~((v3_pre_topc(D, A) & r2_hidden(C, D)) & r1_xboole_0(B, D)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_pre_topc)).
% 2.84/1.43  tff(c_14, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_43, plain, (~r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_24])).
% 2.84/1.43  tff(c_22, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_18, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_53, plain, (![B_46, A_47, C_48]: (r1_xboole_0(B_46, '#skF_1'(A_47, B_46, C_48)) | r2_hidden(C_48, k2_pre_topc(A_47, B_46)) | v2_struct_0(A_47) | ~m1_subset_1(C_48, u1_struct_0(A_47)) | ~m1_subset_1(B_46, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_55, plain, (![C_48]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_48)) | r2_hidden(C_48, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_48, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_53])).
% 2.84/1.43  tff(c_58, plain, (![C_48]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_48)) | r2_hidden(C_48, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_48, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_55])).
% 2.84/1.43  tff(c_60, plain, (![C_49]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_49)) | r2_hidden(C_49, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_49, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_58])).
% 2.84/1.43  tff(c_65, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_43])).
% 2.84/1.43  tff(c_71, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_65])).
% 2.84/1.43  tff(c_80, plain, (![C_54, A_55, B_56]: (r2_hidden(C_54, '#skF_1'(A_55, B_56, C_54)) | r2_hidden(C_54, k2_pre_topc(A_55, B_56)) | v2_struct_0(A_55) | ~m1_subset_1(C_54, u1_struct_0(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_82, plain, (![C_54]: (r2_hidden(C_54, '#skF_1'('#skF_2', '#skF_3', C_54)) | r2_hidden(C_54, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_54, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_80])).
% 2.84/1.43  tff(c_85, plain, (![C_54]: (r2_hidden(C_54, '#skF_1'('#skF_2', '#skF_3', C_54)) | r2_hidden(C_54, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_54, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_82])).
% 2.84/1.43  tff(c_105, plain, (![C_60]: (r2_hidden(C_60, '#skF_1'('#skF_2', '#skF_3', C_60)) | r2_hidden(C_60, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_60, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_85])).
% 2.84/1.43  tff(c_110, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_105, c_43])).
% 2.84/1.43  tff(c_116, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_110])).
% 2.84/1.43  tff(c_72, plain, (![A_50, B_51, C_52]: (v3_pre_topc('#skF_1'(A_50, B_51, C_52), A_50) | r2_hidden(C_52, k2_pre_topc(A_50, B_51)) | v2_struct_0(A_50) | ~m1_subset_1(C_52, u1_struct_0(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_74, plain, (![C_52]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_52), '#skF_2') | r2_hidden(C_52, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_52, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_72])).
% 2.84/1.43  tff(c_77, plain, (![C_52]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_52), '#skF_2') | r2_hidden(C_52, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_52, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_74])).
% 2.84/1.43  tff(c_78, plain, (![C_52]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_52), '#skF_2') | r2_hidden(C_52, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_52, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_77])).
% 2.84/1.43  tff(c_87, plain, (![A_57, B_58, C_59]: (m1_subset_1('#skF_1'(A_57, B_58, C_59), k1_zfmisc_1(u1_struct_0(A_57))) | r2_hidden(C_59, k2_pre_topc(A_57, B_58)) | v2_struct_0(A_57) | ~m1_subset_1(C_59, u1_struct_0(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_38, plain, (![D_41]: (v3_pre_topc('#skF_5', '#skF_2') | ~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_44, plain, (![D_41]: (~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_38])).
% 2.84/1.43  tff(c_97, plain, (![B_58, C_59]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_58, C_59)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_58, C_59)) | ~v3_pre_topc('#skF_1'('#skF_2', B_58, C_59), '#skF_2') | r2_hidden(C_59, k2_pre_topc('#skF_2', B_58)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_59, u1_struct_0('#skF_2')) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_87, c_44])).
% 2.84/1.43  tff(c_103, plain, (![B_58, C_59]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_58, C_59)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_58, C_59)) | ~v3_pre_topc('#skF_1'('#skF_2', B_58, C_59), '#skF_2') | r2_hidden(C_59, k2_pre_topc('#skF_2', B_58)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_59, u1_struct_0('#skF_2')) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_97])).
% 2.84/1.43  tff(c_121, plain, (![B_65, C_66]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_65, C_66)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_65, C_66)) | ~v3_pre_topc('#skF_1'('#skF_2', B_65, C_66), '#skF_2') | r2_hidden(C_66, k2_pre_topc('#skF_2', B_65)) | ~m1_subset_1(C_66, u1_struct_0('#skF_2')) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_103])).
% 2.84/1.43  tff(c_123, plain, (![C_52]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_52)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_52)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden(C_52, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_52, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_78, c_121])).
% 2.84/1.43  tff(c_127, plain, (![C_67]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_67)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_67)) | r2_hidden(C_67, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_67, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_123])).
% 2.84/1.43  tff(c_129, plain, (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_116, c_127])).
% 2.84/1.43  tff(c_133, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_71, c_129])).
% 2.84/1.43  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_133])).
% 2.84/1.43  tff(c_136, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 2.84/1.43  tff(c_173, plain, (![B_80, A_81, C_82]: (r1_xboole_0(B_80, '#skF_1'(A_81, B_80, C_82)) | r2_hidden(C_82, k2_pre_topc(A_81, B_80)) | v2_struct_0(A_81) | ~m1_subset_1(C_82, u1_struct_0(A_81)) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_175, plain, (![C_82]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_82)) | r2_hidden(C_82, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_82, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_173])).
% 2.84/1.43  tff(c_178, plain, (![C_82]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_82)) | r2_hidden(C_82, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_82, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_175])).
% 2.84/1.43  tff(c_180, plain, (![C_83]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_83)) | r2_hidden(C_83, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_83, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_178])).
% 2.84/1.43  tff(c_185, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_180, c_43])).
% 2.84/1.43  tff(c_191, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_185])).
% 2.84/1.43  tff(c_154, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, '#skF_1'(A_77, B_78, C_76)) | r2_hidden(C_76, k2_pre_topc(A_77, B_78)) | v2_struct_0(A_77) | ~m1_subset_1(C_76, u1_struct_0(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_156, plain, (![C_76]: (r2_hidden(C_76, '#skF_1'('#skF_2', '#skF_3', C_76)) | r2_hidden(C_76, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_76, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_154])).
% 2.84/1.43  tff(c_159, plain, (![C_76]: (r2_hidden(C_76, '#skF_1'('#skF_2', '#skF_3', C_76)) | r2_hidden(C_76, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_76, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_156])).
% 2.84/1.43  tff(c_161, plain, (![C_79]: (r2_hidden(C_79, '#skF_1'('#skF_2', '#skF_3', C_79)) | r2_hidden(C_79, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_79, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_159])).
% 2.84/1.43  tff(c_166, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_161, c_43])).
% 2.84/1.43  tff(c_172, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_166])).
% 2.84/1.43  tff(c_146, plain, (![A_72, B_73, C_74]: (v3_pre_topc('#skF_1'(A_72, B_73, C_74), A_72) | r2_hidden(C_74, k2_pre_topc(A_72, B_73)) | v2_struct_0(A_72) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(u1_struct_0(A_72))) | ~l1_pre_topc(A_72))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_148, plain, (![C_74]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_74), '#skF_2') | r2_hidden(C_74, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_74, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_146])).
% 2.84/1.43  tff(c_151, plain, (![C_74]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_74), '#skF_2') | r2_hidden(C_74, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_74, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_148])).
% 2.84/1.43  tff(c_152, plain, (![C_74]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_74), '#skF_2') | r2_hidden(C_74, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_74, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_151])).
% 2.84/1.43  tff(c_192, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_1'(A_84, B_85, C_86), k1_zfmisc_1(u1_struct_0(A_84))) | r2_hidden(C_86, k2_pre_topc(A_84, B_85)) | v2_struct_0(A_84) | ~m1_subset_1(C_86, u1_struct_0(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_36, plain, (![D_41]: (r2_hidden('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_137, plain, (![D_41]: (~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_36])).
% 2.84/1.43  tff(c_202, plain, (![B_85, C_86]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_85, C_86)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_85, C_86)) | ~v3_pre_topc('#skF_1'('#skF_2', B_85, C_86), '#skF_2') | r2_hidden(C_86, k2_pre_topc('#skF_2', B_85)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_86, u1_struct_0('#skF_2')) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_192, c_137])).
% 2.84/1.43  tff(c_208, plain, (![B_85, C_86]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_85, C_86)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_85, C_86)) | ~v3_pre_topc('#skF_1'('#skF_2', B_85, C_86), '#skF_2') | r2_hidden(C_86, k2_pre_topc('#skF_2', B_85)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_86, u1_struct_0('#skF_2')) | ~m1_subset_1(B_85, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_202])).
% 2.84/1.43  tff(c_210, plain, (![B_87, C_88]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_87, C_88)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_87, C_88)) | ~v3_pre_topc('#skF_1'('#skF_2', B_87, C_88), '#skF_2') | r2_hidden(C_88, k2_pre_topc('#skF_2', B_87)) | ~m1_subset_1(C_88, u1_struct_0('#skF_2')) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_208])).
% 2.84/1.43  tff(c_212, plain, (![C_74]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_74)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_74)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden(C_74, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_74, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_152, c_210])).
% 2.84/1.43  tff(c_216, plain, (![C_89]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_89)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_89)) | r2_hidden(C_89, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_89, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_212])).
% 2.84/1.43  tff(c_218, plain, (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_172, c_216])).
% 2.84/1.43  tff(c_222, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_191, c_218])).
% 2.84/1.43  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_222])).
% 2.84/1.43  tff(c_225, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 2.84/1.43  tff(c_235, plain, (![B_94, A_95, C_96]: (r1_xboole_0(B_94, '#skF_1'(A_95, B_94, C_96)) | r2_hidden(C_96, k2_pre_topc(A_95, B_94)) | v2_struct_0(A_95) | ~m1_subset_1(C_96, u1_struct_0(A_95)) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_237, plain, (![C_96]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_96)) | r2_hidden(C_96, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_96, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_235])).
% 2.84/1.43  tff(c_240, plain, (![C_96]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_96)) | r2_hidden(C_96, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_96, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_237])).
% 2.84/1.43  tff(c_242, plain, (![C_97]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_97)) | r2_hidden(C_97, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_97, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_240])).
% 2.84/1.43  tff(c_247, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_242, c_43])).
% 2.84/1.43  tff(c_253, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_247])).
% 2.84/1.43  tff(c_262, plain, (![C_102, A_103, B_104]: (r2_hidden(C_102, '#skF_1'(A_103, B_104, C_102)) | r2_hidden(C_102, k2_pre_topc(A_103, B_104)) | v2_struct_0(A_103) | ~m1_subset_1(C_102, u1_struct_0(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_264, plain, (![C_102]: (r2_hidden(C_102, '#skF_1'('#skF_2', '#skF_3', C_102)) | r2_hidden(C_102, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_102, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_262])).
% 2.84/1.43  tff(c_267, plain, (![C_102]: (r2_hidden(C_102, '#skF_1'('#skF_2', '#skF_3', C_102)) | r2_hidden(C_102, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_102, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_264])).
% 2.84/1.43  tff(c_287, plain, (![C_108]: (r2_hidden(C_108, '#skF_1'('#skF_2', '#skF_3', C_108)) | r2_hidden(C_108, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_108, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_267])).
% 2.84/1.43  tff(c_292, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_287, c_43])).
% 2.84/1.43  tff(c_298, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_292])).
% 2.84/1.43  tff(c_254, plain, (![A_98, B_99, C_100]: (v3_pre_topc('#skF_1'(A_98, B_99, C_100), A_98) | r2_hidden(C_100, k2_pre_topc(A_98, B_99)) | v2_struct_0(A_98) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_256, plain, (![C_100]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_100), '#skF_2') | r2_hidden(C_100, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_100, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_254])).
% 2.84/1.43  tff(c_259, plain, (![C_100]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_100), '#skF_2') | r2_hidden(C_100, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_100, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_256])).
% 2.84/1.43  tff(c_260, plain, (![C_100]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_100), '#skF_2') | r2_hidden(C_100, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_100, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_259])).
% 2.84/1.43  tff(c_269, plain, (![A_105, B_106, C_107]: (m1_subset_1('#skF_1'(A_105, B_106, C_107), k1_zfmisc_1(u1_struct_0(A_105))) | r2_hidden(C_107, k2_pre_topc(A_105, B_106)) | v2_struct_0(A_105) | ~m1_subset_1(C_107, u1_struct_0(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_34, plain, (![D_41]: (r1_xboole_0('#skF_3', '#skF_5') | ~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_226, plain, (![D_41]: (~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_34])).
% 2.84/1.43  tff(c_279, plain, (![B_106, C_107]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_106, C_107)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_106, C_107)) | ~v3_pre_topc('#skF_1'('#skF_2', B_106, C_107), '#skF_2') | r2_hidden(C_107, k2_pre_topc('#skF_2', B_106)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_107, u1_struct_0('#skF_2')) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_269, c_226])).
% 2.84/1.43  tff(c_285, plain, (![B_106, C_107]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_106, C_107)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_106, C_107)) | ~v3_pre_topc('#skF_1'('#skF_2', B_106, C_107), '#skF_2') | r2_hidden(C_107, k2_pre_topc('#skF_2', B_106)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_107, u1_struct_0('#skF_2')) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_279])).
% 2.84/1.43  tff(c_303, plain, (![B_113, C_114]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_113, C_114)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_113, C_114)) | ~v3_pre_topc('#skF_1'('#skF_2', B_113, C_114), '#skF_2') | r2_hidden(C_114, k2_pre_topc('#skF_2', B_113)) | ~m1_subset_1(C_114, u1_struct_0('#skF_2')) | ~m1_subset_1(B_113, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_285])).
% 2.84/1.43  tff(c_305, plain, (![C_100]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_100)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_100)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden(C_100, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_100, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_260, c_303])).
% 2.84/1.43  tff(c_309, plain, (![C_115]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_115)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_115)) | r2_hidden(C_115, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_115, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_305])).
% 2.84/1.43  tff(c_311, plain, (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_298, c_309])).
% 2.84/1.43  tff(c_315, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_253, c_311])).
% 2.84/1.43  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_315])).
% 2.84/1.43  tff(c_318, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 2.84/1.43  tff(c_336, plain, (![B_124, A_125, C_126]: (r1_xboole_0(B_124, '#skF_1'(A_125, B_124, C_126)) | r2_hidden(C_126, k2_pre_topc(A_125, B_124)) | v2_struct_0(A_125) | ~m1_subset_1(C_126, u1_struct_0(A_125)) | ~m1_subset_1(B_124, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_338, plain, (![C_126]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_126)) | r2_hidden(C_126, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_126, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_336])).
% 2.84/1.43  tff(c_341, plain, (![C_126]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_126)) | r2_hidden(C_126, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_126, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_338])).
% 2.84/1.43  tff(c_343, plain, (![C_127]: (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_127)) | r2_hidden(C_127, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_127, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_341])).
% 2.84/1.43  tff(c_348, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_343, c_43])).
% 2.84/1.43  tff(c_354, plain, (r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_348])).
% 2.84/1.43  tff(c_355, plain, (![C_128, A_129, B_130]: (r2_hidden(C_128, '#skF_1'(A_129, B_130, C_128)) | r2_hidden(C_128, k2_pre_topc(A_129, B_130)) | v2_struct_0(A_129) | ~m1_subset_1(C_128, u1_struct_0(A_129)) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_357, plain, (![C_128]: (r2_hidden(C_128, '#skF_1'('#skF_2', '#skF_3', C_128)) | r2_hidden(C_128, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_128, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_355])).
% 2.84/1.43  tff(c_360, plain, (![C_128]: (r2_hidden(C_128, '#skF_1'('#skF_2', '#skF_3', C_128)) | r2_hidden(C_128, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_128, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_357])).
% 2.84/1.43  tff(c_362, plain, (![C_131]: (r2_hidden(C_131, '#skF_1'('#skF_2', '#skF_3', C_131)) | r2_hidden(C_131, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_131, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_360])).
% 2.84/1.43  tff(c_367, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_362, c_43])).
% 2.84/1.43  tff(c_373, plain, (r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_367])).
% 2.84/1.43  tff(c_328, plain, (![A_120, B_121, C_122]: (v3_pre_topc('#skF_1'(A_120, B_121, C_122), A_120) | r2_hidden(C_122, k2_pre_topc(A_120, B_121)) | v2_struct_0(A_120) | ~m1_subset_1(C_122, u1_struct_0(A_120)) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_330, plain, (![C_122]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_122), '#skF_2') | r2_hidden(C_122, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_122, u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_16, c_328])).
% 2.84/1.43  tff(c_333, plain, (![C_122]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_122), '#skF_2') | r2_hidden(C_122, k2_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2') | ~m1_subset_1(C_122, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_330])).
% 2.84/1.43  tff(c_334, plain, (![C_122]: (v3_pre_topc('#skF_1'('#skF_2', '#skF_3', C_122), '#skF_2') | r2_hidden(C_122, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_122, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_22, c_333])).
% 2.84/1.43  tff(c_374, plain, (![A_132, B_133, C_134]: (m1_subset_1('#skF_1'(A_132, B_133, C_134), k1_zfmisc_1(u1_struct_0(A_132))) | r2_hidden(C_134, k2_pre_topc(A_132, B_133)) | v2_struct_0(A_132) | ~m1_subset_1(C_134, u1_struct_0(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_40, plain, (![D_41]: (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_320, plain, (![D_41]: (~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_40])).
% 2.84/1.43  tff(c_384, plain, (![B_133, C_134]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_133, C_134)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_133, C_134)) | ~v3_pre_topc('#skF_1'('#skF_2', B_133, C_134), '#skF_2') | r2_hidden(C_134, k2_pre_topc('#skF_2', B_133)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_134, u1_struct_0('#skF_2')) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_374, c_320])).
% 2.84/1.43  tff(c_390, plain, (![B_133, C_134]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_133, C_134)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_133, C_134)) | ~v3_pre_topc('#skF_1'('#skF_2', B_133, C_134), '#skF_2') | r2_hidden(C_134, k2_pre_topc('#skF_2', B_133)) | v2_struct_0('#skF_2') | ~m1_subset_1(C_134, u1_struct_0('#skF_2')) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_384])).
% 2.84/1.43  tff(c_400, plain, (![B_141, C_142]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', B_141, C_142)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', B_141, C_142)) | ~v3_pre_topc('#skF_1'('#skF_2', B_141, C_142), '#skF_2') | r2_hidden(C_142, k2_pre_topc('#skF_2', B_141)) | ~m1_subset_1(C_142, u1_struct_0('#skF_2')) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_22, c_390])).
% 2.84/1.43  tff(c_402, plain, (![C_122]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_122)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_122)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | r2_hidden(C_122, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_122, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_334, c_400])).
% 2.84/1.43  tff(c_406, plain, (![C_143]: (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', C_143)) | ~r2_hidden('#skF_4', '#skF_1'('#skF_2', '#skF_3', C_143)) | r2_hidden(C_143, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_143, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_402])).
% 2.84/1.43  tff(c_408, plain, (~r1_xboole_0('#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_373, c_406])).
% 2.84/1.43  tff(c_412, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_354, c_408])).
% 2.84/1.43  tff(c_414, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_412])).
% 2.84/1.43  tff(c_415, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_40])).
% 2.84/1.43  tff(c_42, plain, (![D_41]: (r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3')) | ~r1_xboole_0('#skF_3', D_41) | ~r2_hidden('#skF_4', D_41) | ~v3_pre_topc(D_41, '#skF_2') | ~m1_subset_1(D_41, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_417, plain, (![D_144]: (~r1_xboole_0('#skF_3', D_144) | ~r2_hidden('#skF_4', D_144) | ~v3_pre_topc(D_144, '#skF_2') | ~m1_subset_1(D_144, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_43, c_42])).
% 2.84/1.43  tff(c_420, plain, (~r1_xboole_0('#skF_3', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_415, c_417])).
% 2.84/1.43  tff(c_427, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_225, c_318, c_420])).
% 2.84/1.43  tff(c_429, plain, (r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 2.84/1.43  tff(c_26, plain, (r2_hidden('#skF_4', '#skF_5') | ~r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_431, plain, (r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_26])).
% 2.84/1.43  tff(c_28, plain, (v3_pre_topc('#skF_5', '#skF_2') | ~r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_433, plain, (v3_pre_topc('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_28])).
% 2.84/1.43  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~r2_hidden('#skF_4', k2_pre_topc('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.84/1.43  tff(c_435, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_30])).
% 2.84/1.43  tff(c_428, plain, (r1_xboole_0('#skF_3', '#skF_5')), inference(splitRight, [status(thm)], [c_24])).
% 2.84/1.43  tff(c_522, plain, (![B_166, D_167, C_168, A_169]: (~r1_xboole_0(B_166, D_167) | ~r2_hidden(C_168, D_167) | ~v3_pre_topc(D_167, A_169) | ~m1_subset_1(D_167, k1_zfmisc_1(u1_struct_0(A_169))) | ~r2_hidden(C_168, k2_pre_topc(A_169, B_166)) | ~m1_subset_1(C_168, u1_struct_0(A_169)) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_169))) | ~l1_pre_topc(A_169))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.84/1.43  tff(c_526, plain, (![C_170, A_171]: (~r2_hidden(C_170, '#skF_5') | ~v3_pre_topc('#skF_5', A_171) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0(A_171))) | ~r2_hidden(C_170, k2_pre_topc(A_171, '#skF_3')) | ~m1_subset_1(C_170, u1_struct_0(A_171)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_171))) | ~l1_pre_topc(A_171))), inference(resolution, [status(thm)], [c_428, c_522])).
% 2.84/1.43  tff(c_528, plain, (![C_170]: (~r2_hidden(C_170, '#skF_5') | ~v3_pre_topc('#skF_5', '#skF_2') | ~r2_hidden(C_170, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_170, u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_435, c_526])).
% 2.84/1.43  tff(c_532, plain, (![C_172]: (~r2_hidden(C_172, '#skF_5') | ~r2_hidden(C_172, k2_pre_topc('#skF_2', '#skF_3')) | ~m1_subset_1(C_172, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_433, c_528])).
% 2.84/1.43  tff(c_541, plain, (~r2_hidden('#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_429, c_532])).
% 2.84/1.43  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_431, c_541])).
% 2.84/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.43  
% 2.84/1.43  Inference rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Ref     : 0
% 2.84/1.43  #Sup     : 81
% 2.84/1.43  #Fact    : 0
% 2.84/1.43  #Define  : 0
% 2.84/1.43  #Split   : 9
% 2.84/1.43  #Chain   : 0
% 2.84/1.43  #Close   : 0
% 2.84/1.43  
% 2.84/1.43  Ordering : KBO
% 2.84/1.43  
% 2.84/1.43  Simplification rules
% 2.84/1.43  ----------------------
% 2.84/1.43  #Subsume      : 26
% 2.84/1.43  #Demod        : 85
% 2.84/1.43  #Tautology    : 6
% 2.84/1.43  #SimpNegUnit  : 31
% 2.84/1.43  #BackRed      : 0
% 2.84/1.43  
% 2.84/1.43  #Partial instantiations: 0
% 2.84/1.43  #Strategies tried      : 1
% 2.84/1.43  
% 2.84/1.44  Timing (in seconds)
% 2.84/1.44  ----------------------
% 2.84/1.44  Preprocessing        : 0.28
% 2.84/1.44  Parsing              : 0.15
% 2.84/1.44  CNF conversion       : 0.03
% 2.84/1.44  Main loop            : 0.33
% 2.84/1.44  Inferencing          : 0.14
% 2.84/1.44  Reduction            : 0.09
% 2.84/1.44  Demodulation         : 0.06
% 2.84/1.44  BG Simplification    : 0.02
% 2.84/1.44  Subsumption          : 0.07
% 2.84/1.44  Abstraction          : 0.01
% 2.84/1.44  MUC search           : 0.00
% 2.84/1.44  Cooper               : 0.00
% 2.84/1.44  Total                : 0.67
% 2.84/1.44  Index Insertion      : 0.00
% 2.84/1.44  Index Deletion       : 0.00
% 2.84/1.44  Index Matching       : 0.00
% 2.84/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
