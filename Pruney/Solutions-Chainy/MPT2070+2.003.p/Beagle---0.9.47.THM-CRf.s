%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:39 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :  176 (1866 expanded)
%              Number of leaves         :   33 ( 661 expanded)
%              Depth                    :   36
%              Number of atoms          :  797 (12313 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_7 > r1_waybel_7 > v4_pre_topc > v3_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(v2_waybel_0,type,(
    v2_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(r1_waybel_7,type,(
    r1_waybel_7: ( $i * $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r2_waybel_7,type,(
    r2_waybel_7: ( $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v13_waybel_0,type,(
    v13_waybel_0: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v3_waybel_7,type,(
    v3_waybel_7: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> ! [C] :
                  ( ( ~ v1_xboole_0(C)
                    & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(C,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
                 => ( r2_hidden(B,C)
                   => ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => ( r2_waybel_7(A,C,D)
                         => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow19)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> ! [C] :
                ( ( ~ v1_xboole_0(C)
                  & v1_subset_1(C,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                  & v2_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                  & v13_waybel_0(C,k3_yellow_1(k2_struct_0(A)))
                  & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A))))) )
               => ( r2_hidden(B,C)
                 => ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_waybel_7(A,C,D)
                       => r2_hidden(D,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow19)).

tff(f_56,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v1_subset_1(D,u1_struct_0(k3_yellow_1(k2_struct_0(A))))
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r1_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_yellow19)).

tff(f_87,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_hidden(C,k2_pre_topc(A,B))
              <=> ? [D] :
                    ( ~ v1_xboole_0(D)
                    & v2_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v13_waybel_0(D,k3_yellow_1(k2_struct_0(A)))
                    & v3_waybel_7(D,k3_yellow_1(k2_struct_0(A)))
                    & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))
                    & r2_hidden(B,D)
                    & r2_waybel_7(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_yellow19)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_58,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_56,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_78,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_101,plain,(
    ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_40,plain,(
    ! [A_45,B_59] :
      ( m1_subset_1('#skF_4'(A_45,B_59),u1_struct_0(A_45))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_102,plain,(
    ! [A_93,B_94] :
      ( ~ v1_xboole_0('#skF_3'(A_93,B_94))
      | v4_pre_topc(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_105,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_102])).

tff(c_108,plain,
    ( ~ v1_xboole_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_105])).

tff(c_109,plain,(
    ~ v1_xboole_0('#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_108])).

tff(c_111,plain,(
    ! [B_97,A_98] :
      ( r2_hidden(B_97,'#skF_3'(A_98,B_97))
      | v4_pre_topc(B_97,A_98)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_113,plain,
    ( r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_116,plain,
    ( r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_113])).

tff(c_117,plain,(
    r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_116])).

tff(c_46,plain,(
    ! [A_45,B_59] :
      ( v13_waybel_0('#skF_3'(A_45,B_59),k3_yellow_1(k2_struct_0(A_45)))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_48,plain,(
    ! [A_45,B_59] :
      ( v2_waybel_0('#skF_3'(A_45,B_59),k3_yellow_1(k2_struct_0(A_45)))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    ! [A_45,B_59] :
      ( v1_subset_1('#skF_3'(A_45,B_59),u1_struct_0(k3_yellow_1(k2_struct_0(A_45))))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_44,plain,(
    ! [A_45,B_59] :
      ( m1_subset_1('#skF_3'(A_45,B_59),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_45)))))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [A_45,B_59] :
      ( r1_waybel_7(A_45,'#skF_3'(A_45,B_59),'#skF_4'(A_45,B_59))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_209,plain,(
    ! [C_171,A_172,B_173,D_174] :
      ( r2_hidden(C_171,k2_pre_topc(A_172,B_173))
      | ~ r1_waybel_7(A_172,D_174,C_171)
      | ~ r2_hidden(B_173,D_174)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_172)))))
      | ~ v13_waybel_0(D_174,k3_yellow_1(k2_struct_0(A_172)))
      | ~ v2_waybel_0(D_174,k3_yellow_1(k2_struct_0(A_172)))
      | ~ v1_subset_1(D_174,u1_struct_0(k3_yellow_1(k2_struct_0(A_172))))
      | v1_xboole_0(D_174)
      | ~ m1_subset_1(C_171,u1_struct_0(A_172))
      | ~ m1_subset_1(B_173,k1_zfmisc_1(u1_struct_0(A_172)))
      | ~ l1_pre_topc(A_172)
      | ~ v2_pre_topc(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_303,plain,(
    ! [A_216,B_217,B_218] :
      ( r2_hidden('#skF_4'(A_216,B_217),k2_pre_topc(A_216,B_218))
      | ~ r2_hidden(B_218,'#skF_3'(A_216,B_217))
      | ~ m1_subset_1('#skF_3'(A_216,B_217),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_216)))))
      | ~ v13_waybel_0('#skF_3'(A_216,B_217),k3_yellow_1(k2_struct_0(A_216)))
      | ~ v2_waybel_0('#skF_3'(A_216,B_217),k3_yellow_1(k2_struct_0(A_216)))
      | ~ v1_subset_1('#skF_3'(A_216,B_217),u1_struct_0(k3_yellow_1(k2_struct_0(A_216))))
      | v1_xboole_0('#skF_3'(A_216,B_217))
      | ~ m1_subset_1('#skF_4'(A_216,B_217),u1_struct_0(A_216))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(u1_struct_0(A_216)))
      | v4_pre_topc(B_217,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216)
      | ~ v2_pre_topc(A_216)
      | v2_struct_0(A_216) ) ),
    inference(resolution,[status(thm)],[c_38,c_209])).

tff(c_307,plain,(
    ! [A_219,B_220,B_221] :
      ( r2_hidden('#skF_4'(A_219,B_220),k2_pre_topc(A_219,B_221))
      | ~ r2_hidden(B_221,'#skF_3'(A_219,B_220))
      | ~ v13_waybel_0('#skF_3'(A_219,B_220),k3_yellow_1(k2_struct_0(A_219)))
      | ~ v2_waybel_0('#skF_3'(A_219,B_220),k3_yellow_1(k2_struct_0(A_219)))
      | ~ v1_subset_1('#skF_3'(A_219,B_220),u1_struct_0(k3_yellow_1(k2_struct_0(A_219))))
      | v1_xboole_0('#skF_3'(A_219,B_220))
      | ~ m1_subset_1('#skF_4'(A_219,B_220),u1_struct_0(A_219))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_219)))
      | v4_pre_topc(B_220,A_219)
      | ~ m1_subset_1(B_220,k1_zfmisc_1(u1_struct_0(A_219)))
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(resolution,[status(thm)],[c_44,c_303])).

tff(c_311,plain,(
    ! [A_222,B_223,B_224] :
      ( r2_hidden('#skF_4'(A_222,B_223),k2_pre_topc(A_222,B_224))
      | ~ r2_hidden(B_224,'#skF_3'(A_222,B_223))
      | ~ v13_waybel_0('#skF_3'(A_222,B_223),k3_yellow_1(k2_struct_0(A_222)))
      | ~ v2_waybel_0('#skF_3'(A_222,B_223),k3_yellow_1(k2_struct_0(A_222)))
      | v1_xboole_0('#skF_3'(A_222,B_223))
      | ~ m1_subset_1('#skF_4'(A_222,B_223),u1_struct_0(A_222))
      | ~ m1_subset_1(B_224,k1_zfmisc_1(u1_struct_0(A_222)))
      | v4_pre_topc(B_223,A_222)
      | ~ m1_subset_1(B_223,k1_zfmisc_1(u1_struct_0(A_222)))
      | ~ l1_pre_topc(A_222)
      | ~ v2_pre_topc(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_50,c_307])).

tff(c_315,plain,(
    ! [A_225,B_226,B_227] :
      ( r2_hidden('#skF_4'(A_225,B_226),k2_pre_topc(A_225,B_227))
      | ~ r2_hidden(B_227,'#skF_3'(A_225,B_226))
      | ~ v13_waybel_0('#skF_3'(A_225,B_226),k3_yellow_1(k2_struct_0(A_225)))
      | v1_xboole_0('#skF_3'(A_225,B_226))
      | ~ m1_subset_1('#skF_4'(A_225,B_226),u1_struct_0(A_225))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_225)))
      | v4_pre_topc(B_226,A_225)
      | ~ m1_subset_1(B_226,k1_zfmisc_1(u1_struct_0(A_225)))
      | ~ l1_pre_topc(A_225)
      | ~ v2_pre_topc(A_225)
      | v2_struct_0(A_225) ) ),
    inference(resolution,[status(thm)],[c_48,c_311])).

tff(c_318,plain,(
    ! [A_45,B_59,B_227] :
      ( r2_hidden('#skF_4'(A_45,B_59),k2_pre_topc(A_45,B_227))
      | ~ r2_hidden(B_227,'#skF_3'(A_45,B_59))
      | v1_xboole_0('#skF_3'(A_45,B_59))
      | ~ m1_subset_1('#skF_4'(A_45,B_59),u1_struct_0(A_45))
      | ~ m1_subset_1(B_227,k1_zfmisc_1(u1_struct_0(A_45)))
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_46,c_315])).

tff(c_320,plain,(
    ! [A_230,B_231,B_232] :
      ( r2_hidden('#skF_4'(A_230,B_231),k2_pre_topc(A_230,B_232))
      | ~ r2_hidden(B_232,'#skF_3'(A_230,B_231))
      | v1_xboole_0('#skF_3'(A_230,B_231))
      | ~ m1_subset_1('#skF_4'(A_230,B_231),u1_struct_0(A_230))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_230)))
      | v4_pre_topc(B_231,A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_46,c_315])).

tff(c_22,plain,(
    ! [B_35,A_23,C_41] :
      ( r2_hidden(B_35,'#skF_2'(A_23,B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_339,plain,(
    ! [B_239,A_240,B_241] :
      ( r2_hidden(B_239,'#skF_2'(A_240,B_239,'#skF_4'(A_240,B_241)))
      | ~ r2_hidden(B_239,'#skF_3'(A_240,B_241))
      | v1_xboole_0('#skF_3'(A_240,B_241))
      | ~ m1_subset_1('#skF_4'(A_240,B_241),u1_struct_0(A_240))
      | ~ m1_subset_1(B_239,k1_zfmisc_1(u1_struct_0(A_240)))
      | v4_pre_topc(B_241,A_240)
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0(A_240)))
      | ~ l1_pre_topc(A_240)
      | ~ v2_pre_topc(A_240)
      | v2_struct_0(A_240) ) ),
    inference(resolution,[status(thm)],[c_320,c_22])).

tff(c_28,plain,(
    ! [A_23,B_35,C_41] :
      ( v13_waybel_0('#skF_2'(A_23,B_35,C_41),k3_yellow_1(k2_struct_0(A_23)))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    ! [A_23,B_35,C_41] :
      ( v2_waybel_0('#skF_2'(A_23,B_35,C_41),k3_yellow_1(k2_struct_0(A_23)))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_23,B_35,C_41] :
      ( v3_waybel_7('#skF_2'(A_23,B_35,C_41),k3_yellow_1(k2_struct_0(A_23)))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_23,B_35,C_41] :
      ( m1_subset_1('#skF_2'(A_23,B_35,C_41),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_23)))))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_148,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_waybel_7(A_127,'#skF_2'(A_127,B_128,C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc(A_127,B_128))
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_152,plain,(
    ! [C_129] :
      ( r2_waybel_7('#skF_5','#skF_2'('#skF_5','#skF_6',C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_148])).

tff(c_156,plain,(
    ! [C_129] :
      ( r2_waybel_7('#skF_5','#skF_2'('#skF_5','#skF_6',C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_152])).

tff(c_157,plain,(
    ! [C_129] :
      ( r2_waybel_7('#skF_5','#skF_2'('#skF_5','#skF_6',C_129),C_129)
      | ~ r2_hidden(C_129,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_129,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_156])).

tff(c_100,plain,(
    ! [D_92,C_90] :
      ( v4_pre_topc('#skF_6','#skF_5')
      | r2_hidden(D_92,'#skF_6')
      | ~ r2_waybel_7('#skF_5',C_90,D_92)
      | ~ m1_subset_1(D_92,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_90,k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_162,plain,(
    ! [D_137,C_138] :
      ( r2_hidden(D_137,'#skF_6')
      | ~ r2_waybel_7('#skF_5',C_138,D_137)
      | ~ m1_subset_1(D_137,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_6',C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7(C_138,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0(C_138,k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0(C_138,k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0(C_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_100])).

tff(c_250,plain,(
    ! [C_197] :
      ( r2_hidden(C_197,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_197))
      | ~ m1_subset_1('#skF_2'('#skF_5','#skF_6',C_197),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7('#skF_2'('#skF_5','#skF_6',C_197),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_197),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_197),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_197))
      | ~ r2_hidden(C_197,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_197,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_157,c_162])).

tff(c_254,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | ~ v3_waybel_7('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_24,c_250])).

tff(c_257,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | ~ v3_waybel_7('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_254])).

tff(c_259,plain,(
    ! [C_198] :
      ( r2_hidden(C_198,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_198))
      | ~ v3_waybel_7('#skF_2'('#skF_5','#skF_6',C_198),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_198),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_198),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_198))
      | ~ r2_hidden(C_198,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_198,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_257])).

tff(c_263,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_259])).

tff(c_266,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_263])).

tff(c_268,plain,(
    ! [C_199] :
      ( r2_hidden(C_199,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_199))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_199),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_2'('#skF_5','#skF_6',C_199),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_199))
      | ~ r2_hidden(C_199,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_199,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_266])).

tff(c_272,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_30,c_268])).

tff(c_275,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_41),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_272])).

tff(c_277,plain,(
    ! [C_200] :
      ( r2_hidden(C_200,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_200))
      | ~ v13_waybel_0('#skF_2'('#skF_5','#skF_6',C_200),k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_200))
      | ~ r2_hidden(C_200,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_200,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_275])).

tff(c_281,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_277])).

tff(c_284,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_281])).

tff(c_285,plain,(
    ! [C_41] :
      ( r2_hidden(C_41,'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_2'('#skF_5','#skF_6',C_41))
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6',C_41))
      | ~ r2_hidden(C_41,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_41,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_284])).

tff(c_342,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_4'('#skF_5',B_241),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_241)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_241),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_241))
      | v1_xboole_0('#skF_3'('#skF_5',B_241))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_241),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_241,'#skF_5')
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_339,c_285])).

tff(c_348,plain,(
    ! [B_241] :
      ( r2_hidden('#skF_4'('#skF_5',B_241),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_241)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_241),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_241))
      | v1_xboole_0('#skF_3'('#skF_5',B_241))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_241),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_241,'#skF_5')
      | ~ m1_subset_1(B_241,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_342])).

tff(c_385,plain,(
    ! [B_248] :
      ( r2_hidden('#skF_4'('#skF_5',B_248),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_248)))
      | ~ r2_hidden('#skF_4'('#skF_5',B_248),k2_pre_topc('#skF_5','#skF_6'))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_248))
      | v1_xboole_0('#skF_3'('#skF_5',B_248))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_248),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_248,'#skF_5')
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_348])).

tff(c_389,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_59),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_59))
      | v1_xboole_0('#skF_3'('#skF_5',B_59))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_59),u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v4_pre_topc(B_59,'#skF_5')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_318,c_385])).

tff(c_392,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_59),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_59))
      | v1_xboole_0('#skF_3'('#skF_5',B_59))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_59),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_59,'#skF_5')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_389])).

tff(c_394,plain,(
    ! [B_249] :
      ( r2_hidden('#skF_4'('#skF_5',B_249),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_249)))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_249))
      | v1_xboole_0('#skF_3'('#skF_5',B_249))
      | ~ m1_subset_1('#skF_4'('#skF_5',B_249),u1_struct_0('#skF_5'))
      | v4_pre_topc(B_249,'#skF_5')
      | ~ m1_subset_1(B_249,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_392])).

tff(c_398,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_59),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_59))
      | v1_xboole_0('#skF_3'('#skF_5',B_59))
      | v4_pre_topc(B_59,'#skF_5')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_40,c_394])).

tff(c_401,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_4'('#skF_5',B_59),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_59)))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_59))
      | v1_xboole_0('#skF_3'('#skF_5',B_59))
      | v4_pre_topc(B_59,'#skF_5')
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_398])).

tff(c_403,plain,(
    ! [B_250] :
      ( r2_hidden('#skF_4'('#skF_5',B_250),'#skF_6')
      | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5',B_250)))
      | ~ r2_hidden('#skF_6','#skF_3'('#skF_5',B_250))
      | v1_xboole_0('#skF_3'('#skF_5',B_250))
      | v4_pre_topc(B_250,'#skF_5')
      | ~ m1_subset_1(B_250,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_401])).

tff(c_406,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | ~ r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_403])).

tff(c_409,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6')))
    | v1_xboole_0('#skF_3'('#skF_5','#skF_6'))
    | v4_pre_topc('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_406])).

tff(c_410,plain,
    ( r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6')
    | v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_109,c_409])).

tff(c_411,plain,(
    v1_xboole_0('#skF_2'('#skF_5','#skF_6','#skF_4'('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_410])).

tff(c_32,plain,(
    ! [A_23,B_35,C_41] :
      ( ~ v1_xboole_0('#skF_2'(A_23,B_35,C_41))
      | ~ r2_hidden(C_41,k2_pre_topc(A_23,B_35))
      | ~ m1_subset_1(C_41,u1_struct_0(A_23))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23)
      | v2_struct_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_334,plain,(
    ! [A_230,B_232,B_231] :
      ( ~ v1_xboole_0('#skF_2'(A_230,B_232,'#skF_4'(A_230,B_231)))
      | ~ r2_hidden(B_232,'#skF_3'(A_230,B_231))
      | v1_xboole_0('#skF_3'(A_230,B_231))
      | ~ m1_subset_1('#skF_4'(A_230,B_231),u1_struct_0(A_230))
      | ~ m1_subset_1(B_232,k1_zfmisc_1(u1_struct_0(A_230)))
      | v4_pre_topc(B_231,A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_320,c_32])).

tff(c_413,plain,
    ( ~ r2_hidden('#skF_6','#skF_3'('#skF_5','#skF_6'))
    | v1_xboole_0('#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_411,c_334])).

tff(c_416,plain,
    ( v1_xboole_0('#skF_3'('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5'))
    | v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_117,c_413])).

tff(c_417,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_109,c_416])).

tff(c_420,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_417])).

tff(c_423,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_420])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_423])).

tff(c_426,plain,(
    r2_hidden('#skF_4'('#skF_5','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_410])).

tff(c_36,plain,(
    ! [A_45,B_59] :
      ( ~ r2_hidden('#skF_4'(A_45,B_59),B_59)
      | v4_pre_topc(B_59,A_45)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_429,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_426,c_36])).

tff(c_432,plain,
    ( v4_pre_topc('#skF_6','#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_429])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101,c_432])).

tff(c_436,plain,(
    v4_pre_topc('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_66,plain,
    ( m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_444,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_66])).

tff(c_68,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_438,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_68])).

tff(c_435,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_450,plain,(
    v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_76])).

tff(c_74,plain,
    ( v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_446,plain,(
    v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_74])).

tff(c_72,plain,
    ( v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_448,plain,(
    v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_72])).

tff(c_70,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_452,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_70])).

tff(c_64,plain,
    ( r2_waybel_7('#skF_5','#skF_7','#skF_8')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_442,plain,(
    r2_waybel_7('#skF_5','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_64])).

tff(c_567,plain,(
    ! [C_320,A_321,B_322,D_323] :
      ( r2_hidden(C_320,k2_pre_topc(A_321,B_322))
      | ~ r2_waybel_7(A_321,D_323,C_320)
      | ~ r2_hidden(B_322,D_323)
      | ~ m1_subset_1(D_323,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_321)))))
      | ~ v3_waybel_7(D_323,k3_yellow_1(k2_struct_0(A_321)))
      | ~ v13_waybel_0(D_323,k3_yellow_1(k2_struct_0(A_321)))
      | ~ v2_waybel_0(D_323,k3_yellow_1(k2_struct_0(A_321)))
      | v1_xboole_0(D_323)
      | ~ m1_subset_1(C_320,u1_struct_0(A_321))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0(A_321)))
      | ~ l1_pre_topc(A_321)
      | ~ v2_pre_topc(A_321)
      | v2_struct_0(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_571,plain,(
    ! [B_322] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_322))
      | ~ r2_hidden(B_322,'#skF_7')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v3_waybel_7('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v13_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_7',k3_yellow_1(k2_struct_0('#skF_5')))
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_442,c_567])).

tff(c_578,plain,(
    ! [B_322] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_322))
      | ~ r2_hidden(B_322,'#skF_7')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(B_322,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_444,c_450,c_446,c_448,c_452,c_571])).

tff(c_580,plain,(
    ! [B_324] :
      ( r2_hidden('#skF_8',k2_pre_topc('#skF_5',B_324))
      | ~ r2_hidden(B_324,'#skF_7')
      | ~ m1_subset_1(B_324,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_435,c_578])).

tff(c_583,plain,
    ( r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_54,c_580])).

tff(c_586,plain,(
    r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_583])).

tff(c_10,plain,(
    ! [A_1,B_13,C_19] :
      ( v13_waybel_0('#skF_1'(A_1,B_13,C_19),k3_yellow_1(k2_struct_0(A_1)))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( v2_waybel_0('#skF_1'(A_1,B_13,C_19),k3_yellow_1(k2_struct_0(A_1)))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_1)))))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [A_1,B_13,C_19] :
      ( v1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(k3_yellow_1(k2_struct_0(A_1))))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_1,B_13,C_19] :
      ( ~ v1_xboole_0('#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_592,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_586,c_16])).

tff(c_605,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_444,c_592])).

tff(c_606,plain,(
    ~ v1_xboole_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_605])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_8','#skF_6')
    | ~ v4_pre_topc('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_62])).

tff(c_6,plain,(
    ! [B_13,A_1,C_19] :
      ( r2_hidden(B_13,'#skF_1'(A_1,B_13,C_19))
      | ~ r2_hidden(C_19,k2_pre_topc(A_1,B_13))
      | ~ m1_subset_1(C_19,u1_struct_0(A_1))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_588,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_586,c_6])).

tff(c_597,plain,
    ( r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_6','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_444,c_588])).

tff(c_598,plain,(
    r2_hidden('#skF_6','#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_597])).

tff(c_495,plain,(
    ! [A_281,B_282,C_283] :
      ( r1_waybel_7(A_281,'#skF_1'(A_281,B_282,C_283),C_283)
      | ~ r2_hidden(C_283,k2_pre_topc(A_281,B_282))
      | ~ m1_subset_1(C_283,u1_struct_0(A_281))
      | ~ m1_subset_1(B_282,k1_zfmisc_1(u1_struct_0(A_281)))
      | ~ l1_pre_topc(A_281)
      | ~ v2_pre_topc(A_281)
      | v2_struct_0(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_501,plain,(
    ! [C_283] :
      ( r1_waybel_7('#skF_5','#skF_1'('#skF_5','#skF_6',C_283),C_283)
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_54,c_495])).

tff(c_506,plain,(
    ! [C_283] :
      ( r1_waybel_7('#skF_5','#skF_1'('#skF_5','#skF_6',C_283),C_283)
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_501])).

tff(c_507,plain,(
    ! [C_283] :
      ( r1_waybel_7('#skF_5','#skF_1'('#skF_5','#skF_6',C_283),C_283)
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_506])).

tff(c_622,plain,(
    ! [D_332,B_333,A_334,C_335] :
      ( r2_hidden(D_332,B_333)
      | ~ r1_waybel_7(A_334,C_335,D_332)
      | ~ m1_subset_1(D_332,u1_struct_0(A_334))
      | ~ r2_hidden(B_333,C_335)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_334)))))
      | ~ v13_waybel_0(C_335,k3_yellow_1(k2_struct_0(A_334)))
      | ~ v2_waybel_0(C_335,k3_yellow_1(k2_struct_0(A_334)))
      | ~ v1_subset_1(C_335,u1_struct_0(k3_yellow_1(k2_struct_0(A_334))))
      | v1_xboole_0(C_335)
      | ~ v4_pre_topc(B_333,A_334)
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334)
      | v2_struct_0(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_624,plain,(
    ! [C_283,B_333] :
      ( r2_hidden(C_283,B_333)
      | ~ r2_hidden(B_333,'#skF_1'('#skF_5','#skF_6',C_283))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',C_283),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6',C_283),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6',C_283),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_1'('#skF_5','#skF_6',C_283),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_1'('#skF_5','#skF_6',C_283))
      | ~ v4_pre_topc(B_333,'#skF_5')
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_507,c_622])).

tff(c_629,plain,(
    ! [C_283,B_333] :
      ( r2_hidden(C_283,B_333)
      | ~ r2_hidden(B_333,'#skF_1'('#skF_5','#skF_6',C_283))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',C_283),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6',C_283),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6',C_283),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_1'('#skF_5','#skF_6',C_283),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_1'('#skF_5','#skF_6',C_283))
      | ~ v4_pre_topc(B_333,'#skF_5')
      | ~ m1_subset_1(B_333,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_5')
      | ~ r2_hidden(C_283,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_624])).

tff(c_697,plain,(
    ! [C_380,B_381] :
      ( r2_hidden(C_380,B_381)
      | ~ r2_hidden(B_381,'#skF_1'('#skF_5','#skF_6',C_380))
      | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6',C_380),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
      | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6',C_380),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6',C_380),k3_yellow_1(k2_struct_0('#skF_5')))
      | ~ v1_subset_1('#skF_1'('#skF_5','#skF_6',C_380),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
      | v1_xboole_0('#skF_1'('#skF_5','#skF_6',C_380))
      | ~ v4_pre_topc(B_381,'#skF_5')
      | ~ m1_subset_1(B_381,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r2_hidden(C_380,k2_pre_topc('#skF_5','#skF_6'))
      | ~ m1_subset_1(C_380,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_629])).

tff(c_699,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0('#skF_1'('#skF_5','#skF_6','#skF_8'))
    | ~ v4_pre_topc('#skF_6','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_598,c_697])).

tff(c_702,plain,
    ( r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))
    | v1_xboole_0('#skF_1'('#skF_5','#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_586,c_54,c_436,c_699])).

tff(c_703,plain,
    ( ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))
    | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(negUnitSimplification,[status(thm)],[c_606,c_440,c_702])).

tff(c_704,plain,(
    ~ v1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_703])).

tff(c_707,plain,
    ( ~ r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_704])).

tff(c_710,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_444,c_586,c_707])).

tff(c_712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_710])).

tff(c_713,plain,
    ( ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(splitRight,[status(thm)],[c_703])).

tff(c_715,plain,(
    ~ m1_subset_1('#skF_1'('#skF_5','#skF_6','#skF_8'),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_718,plain,
    ( ~ r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_715])).

tff(c_721,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_444,c_586,c_718])).

tff(c_723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_721])).

tff(c_724,plain,
    ( ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5')))
    | ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_749,plain,(
    ~ v2_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_752,plain,
    ( ~ r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_749])).

tff(c_755,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_444,c_586,c_752])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_755])).

tff(c_758,plain,(
    ~ v13_waybel_0('#skF_1'('#skF_5','#skF_6','#skF_8'),k3_yellow_1(k2_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_762,plain,
    ( ~ r2_hidden('#skF_8',k2_pre_topc('#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_758])).

tff(c_765,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_444,c_586,c_762])).

tff(c_767,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_765])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.29  % Computer   : n011.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 10:38:12 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.30  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.64  
% 4.17/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.64  %$ r2_waybel_7 > r1_waybel_7 > v4_pre_topc > v3_waybel_7 > v2_waybel_0 > v1_subset_1 > v13_waybel_0 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k2_pre_topc > #nlpp > u1_struct_0 > k3_yellow_1 > k2_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 4.17/1.64  
% 4.17/1.64  %Foreground sorts:
% 4.17/1.64  
% 4.17/1.64  
% 4.17/1.64  %Background operators:
% 4.17/1.64  
% 4.17/1.64  
% 4.17/1.64  %Foreground operators:
% 4.17/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.17/1.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.17/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.17/1.64  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 4.17/1.64  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 4.17/1.64  tff(v2_waybel_0, type, v2_waybel_0: ($i * $i) > $o).
% 4.17/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.17/1.64  tff('#skF_7', type, '#skF_7': $i).
% 4.17/1.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.17/1.64  tff('#skF_5', type, '#skF_5': $i).
% 4.17/1.64  tff('#skF_6', type, '#skF_6': $i).
% 4.17/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.17/1.64  tff(r1_waybel_7, type, r1_waybel_7: ($i * $i * $i) > $o).
% 4.17/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.17/1.64  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.17/1.64  tff('#skF_8', type, '#skF_8': $i).
% 4.17/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.64  tff(r2_waybel_7, type, r2_waybel_7: ($i * $i * $i) > $o).
% 4.17/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.64  tff(v13_waybel_0, type, v13_waybel_0: ($i * $i) > $o).
% 4.17/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.17/1.64  tff(v3_waybel_7, type, v3_waybel_7: ($i * $i) > $o).
% 4.17/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.17/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.17/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.17/1.64  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.17/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.17/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.17/1.64  
% 4.17/1.67  tff(f_154, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v1_xboole_0(C) & v2_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v3_waybel_7(C, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_hidden(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_waybel_7(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow19)).
% 4.17/1.67  tff(f_120, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (![C]: (((((~v1_xboole_0(C) & v1_subset_1(C, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(C, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) => (r2_hidden(B, C) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_waybel_7(A, C, D) => r2_hidden(D, B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow19)).
% 4.17/1.67  tff(f_56, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v1_xboole_0(D) & v1_subset_1(D, u1_struct_0(k3_yellow_1(k2_struct_0(A))))) & v2_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) & r2_hidden(B, D)) & r1_waybel_7(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_yellow19)).
% 4.17/1.67  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k2_pre_topc(A, B)) <=> (?[D]: ((((((~v1_xboole_0(D) & v2_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v13_waybel_0(D, k3_yellow_1(k2_struct_0(A)))) & v3_waybel_7(D, k3_yellow_1(k2_struct_0(A)))) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A)))))) & r2_hidden(B, D)) & r2_waybel_7(A, D, C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_yellow19)).
% 4.17/1.67  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_58, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_56, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_78, plain, (~v1_xboole_0('#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_101, plain, (~v4_pre_topc('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 4.17/1.67  tff(c_40, plain, (![A_45, B_59]: (m1_subset_1('#skF_4'(A_45, B_59), u1_struct_0(A_45)) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_102, plain, (![A_93, B_94]: (~v1_xboole_0('#skF_3'(A_93, B_94)) | v4_pre_topc(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_105, plain, (~v1_xboole_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_102])).
% 4.17/1.67  tff(c_108, plain, (~v1_xboole_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_105])).
% 4.17/1.67  tff(c_109, plain, (~v1_xboole_0('#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_108])).
% 4.17/1.67  tff(c_111, plain, (![B_97, A_98]: (r2_hidden(B_97, '#skF_3'(A_98, B_97)) | v4_pre_topc(B_97, A_98) | ~m1_subset_1(B_97, k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_113, plain, (r2_hidden('#skF_6', '#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_54, c_111])).
% 4.17/1.67  tff(c_116, plain, (r2_hidden('#skF_6', '#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_113])).
% 4.17/1.67  tff(c_117, plain, (r2_hidden('#skF_6', '#skF_3'('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_116])).
% 4.17/1.67  tff(c_46, plain, (![A_45, B_59]: (v13_waybel_0('#skF_3'(A_45, B_59), k3_yellow_1(k2_struct_0(A_45))) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_48, plain, (![A_45, B_59]: (v2_waybel_0('#skF_3'(A_45, B_59), k3_yellow_1(k2_struct_0(A_45))) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_50, plain, (![A_45, B_59]: (v1_subset_1('#skF_3'(A_45, B_59), u1_struct_0(k3_yellow_1(k2_struct_0(A_45)))) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_44, plain, (![A_45, B_59]: (m1_subset_1('#skF_3'(A_45, B_59), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_45))))) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_38, plain, (![A_45, B_59]: (r1_waybel_7(A_45, '#skF_3'(A_45, B_59), '#skF_4'(A_45, B_59)) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_209, plain, (![C_171, A_172, B_173, D_174]: (r2_hidden(C_171, k2_pre_topc(A_172, B_173)) | ~r1_waybel_7(A_172, D_174, C_171) | ~r2_hidden(B_173, D_174) | ~m1_subset_1(D_174, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_172))))) | ~v13_waybel_0(D_174, k3_yellow_1(k2_struct_0(A_172))) | ~v2_waybel_0(D_174, k3_yellow_1(k2_struct_0(A_172))) | ~v1_subset_1(D_174, u1_struct_0(k3_yellow_1(k2_struct_0(A_172)))) | v1_xboole_0(D_174) | ~m1_subset_1(C_171, u1_struct_0(A_172)) | ~m1_subset_1(B_173, k1_zfmisc_1(u1_struct_0(A_172))) | ~l1_pre_topc(A_172) | ~v2_pre_topc(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_303, plain, (![A_216, B_217, B_218]: (r2_hidden('#skF_4'(A_216, B_217), k2_pre_topc(A_216, B_218)) | ~r2_hidden(B_218, '#skF_3'(A_216, B_217)) | ~m1_subset_1('#skF_3'(A_216, B_217), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_216))))) | ~v13_waybel_0('#skF_3'(A_216, B_217), k3_yellow_1(k2_struct_0(A_216))) | ~v2_waybel_0('#skF_3'(A_216, B_217), k3_yellow_1(k2_struct_0(A_216))) | ~v1_subset_1('#skF_3'(A_216, B_217), u1_struct_0(k3_yellow_1(k2_struct_0(A_216)))) | v1_xboole_0('#skF_3'(A_216, B_217)) | ~m1_subset_1('#skF_4'(A_216, B_217), u1_struct_0(A_216)) | ~m1_subset_1(B_218, k1_zfmisc_1(u1_struct_0(A_216))) | v4_pre_topc(B_217, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_216))) | ~l1_pre_topc(A_216) | ~v2_pre_topc(A_216) | v2_struct_0(A_216))), inference(resolution, [status(thm)], [c_38, c_209])).
% 4.17/1.67  tff(c_307, plain, (![A_219, B_220, B_221]: (r2_hidden('#skF_4'(A_219, B_220), k2_pre_topc(A_219, B_221)) | ~r2_hidden(B_221, '#skF_3'(A_219, B_220)) | ~v13_waybel_0('#skF_3'(A_219, B_220), k3_yellow_1(k2_struct_0(A_219))) | ~v2_waybel_0('#skF_3'(A_219, B_220), k3_yellow_1(k2_struct_0(A_219))) | ~v1_subset_1('#skF_3'(A_219, B_220), u1_struct_0(k3_yellow_1(k2_struct_0(A_219)))) | v1_xboole_0('#skF_3'(A_219, B_220)) | ~m1_subset_1('#skF_4'(A_219, B_220), u1_struct_0(A_219)) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_219))) | v4_pre_topc(B_220, A_219) | ~m1_subset_1(B_220, k1_zfmisc_1(u1_struct_0(A_219))) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(resolution, [status(thm)], [c_44, c_303])).
% 4.17/1.67  tff(c_311, plain, (![A_222, B_223, B_224]: (r2_hidden('#skF_4'(A_222, B_223), k2_pre_topc(A_222, B_224)) | ~r2_hidden(B_224, '#skF_3'(A_222, B_223)) | ~v13_waybel_0('#skF_3'(A_222, B_223), k3_yellow_1(k2_struct_0(A_222))) | ~v2_waybel_0('#skF_3'(A_222, B_223), k3_yellow_1(k2_struct_0(A_222))) | v1_xboole_0('#skF_3'(A_222, B_223)) | ~m1_subset_1('#skF_4'(A_222, B_223), u1_struct_0(A_222)) | ~m1_subset_1(B_224, k1_zfmisc_1(u1_struct_0(A_222))) | v4_pre_topc(B_223, A_222) | ~m1_subset_1(B_223, k1_zfmisc_1(u1_struct_0(A_222))) | ~l1_pre_topc(A_222) | ~v2_pre_topc(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_50, c_307])).
% 4.17/1.67  tff(c_315, plain, (![A_225, B_226, B_227]: (r2_hidden('#skF_4'(A_225, B_226), k2_pre_topc(A_225, B_227)) | ~r2_hidden(B_227, '#skF_3'(A_225, B_226)) | ~v13_waybel_0('#skF_3'(A_225, B_226), k3_yellow_1(k2_struct_0(A_225))) | v1_xboole_0('#skF_3'(A_225, B_226)) | ~m1_subset_1('#skF_4'(A_225, B_226), u1_struct_0(A_225)) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_225))) | v4_pre_topc(B_226, A_225) | ~m1_subset_1(B_226, k1_zfmisc_1(u1_struct_0(A_225))) | ~l1_pre_topc(A_225) | ~v2_pre_topc(A_225) | v2_struct_0(A_225))), inference(resolution, [status(thm)], [c_48, c_311])).
% 4.17/1.67  tff(c_318, plain, (![A_45, B_59, B_227]: (r2_hidden('#skF_4'(A_45, B_59), k2_pre_topc(A_45, B_227)) | ~r2_hidden(B_227, '#skF_3'(A_45, B_59)) | v1_xboole_0('#skF_3'(A_45, B_59)) | ~m1_subset_1('#skF_4'(A_45, B_59), u1_struct_0(A_45)) | ~m1_subset_1(B_227, k1_zfmisc_1(u1_struct_0(A_45))) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(resolution, [status(thm)], [c_46, c_315])).
% 4.17/1.67  tff(c_320, plain, (![A_230, B_231, B_232]: (r2_hidden('#skF_4'(A_230, B_231), k2_pre_topc(A_230, B_232)) | ~r2_hidden(B_232, '#skF_3'(A_230, B_231)) | v1_xboole_0('#skF_3'(A_230, B_231)) | ~m1_subset_1('#skF_4'(A_230, B_231), u1_struct_0(A_230)) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_230))) | v4_pre_topc(B_231, A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_46, c_315])).
% 4.17/1.67  tff(c_22, plain, (![B_35, A_23, C_41]: (r2_hidden(B_35, '#skF_2'(A_23, B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_339, plain, (![B_239, A_240, B_241]: (r2_hidden(B_239, '#skF_2'(A_240, B_239, '#skF_4'(A_240, B_241))) | ~r2_hidden(B_239, '#skF_3'(A_240, B_241)) | v1_xboole_0('#skF_3'(A_240, B_241)) | ~m1_subset_1('#skF_4'(A_240, B_241), u1_struct_0(A_240)) | ~m1_subset_1(B_239, k1_zfmisc_1(u1_struct_0(A_240))) | v4_pre_topc(B_241, A_240) | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0(A_240))) | ~l1_pre_topc(A_240) | ~v2_pre_topc(A_240) | v2_struct_0(A_240))), inference(resolution, [status(thm)], [c_320, c_22])).
% 4.17/1.67  tff(c_28, plain, (![A_23, B_35, C_41]: (v13_waybel_0('#skF_2'(A_23, B_35, C_41), k3_yellow_1(k2_struct_0(A_23))) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_30, plain, (![A_23, B_35, C_41]: (v2_waybel_0('#skF_2'(A_23, B_35, C_41), k3_yellow_1(k2_struct_0(A_23))) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_26, plain, (![A_23, B_35, C_41]: (v3_waybel_7('#skF_2'(A_23, B_35, C_41), k3_yellow_1(k2_struct_0(A_23))) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_24, plain, (![A_23, B_35, C_41]: (m1_subset_1('#skF_2'(A_23, B_35, C_41), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_23))))) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_148, plain, (![A_127, B_128, C_129]: (r2_waybel_7(A_127, '#skF_2'(A_127, B_128, C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc(A_127, B_128)) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_152, plain, (![C_129]: (r2_waybel_7('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_129, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_148])).
% 4.17/1.67  tff(c_156, plain, (![C_129]: (r2_waybel_7('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_129, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_152])).
% 4.17/1.67  tff(c_157, plain, (![C_129]: (r2_waybel_7('#skF_5', '#skF_2'('#skF_5', '#skF_6', C_129), C_129) | ~r2_hidden(C_129, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_129, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_156])).
% 4.17/1.67  tff(c_100, plain, (![D_92, C_90]: (v4_pre_topc('#skF_6', '#skF_5') | r2_hidden(D_92, '#skF_6') | ~r2_waybel_7('#skF_5', C_90, D_92) | ~m1_subset_1(D_92, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_90, k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0(C_90))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_162, plain, (![D_137, C_138]: (r2_hidden(D_137, '#skF_6') | ~r2_waybel_7('#skF_5', C_138, D_137) | ~m1_subset_1(D_137, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7(C_138, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0(C_138, k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0(C_138, k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0(C_138))), inference(negUnitSimplification, [status(thm)], [c_101, c_100])).
% 4.17/1.67  tff(c_250, plain, (![C_197]: (r2_hidden(C_197, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_197)) | ~m1_subset_1('#skF_2'('#skF_5', '#skF_6', C_197), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7('#skF_2'('#skF_5', '#skF_6', C_197), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_197), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_197), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_197)) | ~r2_hidden(C_197, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_197, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_157, c_162])).
% 4.17/1.67  tff(c_254, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | ~v3_waybel_7('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_24, c_250])).
% 4.17/1.67  tff(c_257, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | ~v3_waybel_7('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_254])).
% 4.17/1.67  tff(c_259, plain, (![C_198]: (r2_hidden(C_198, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_198)) | ~v3_waybel_7('#skF_2'('#skF_5', '#skF_6', C_198), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_198), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_198), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_198)) | ~r2_hidden(C_198, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_198, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_257])).
% 4.17/1.67  tff(c_263, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_26, c_259])).
% 4.17/1.67  tff(c_266, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_263])).
% 4.17/1.67  tff(c_268, plain, (![C_199]: (r2_hidden(C_199, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_199)) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_199), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_2'('#skF_5', '#skF_6', C_199), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_199)) | ~r2_hidden(C_199, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_199, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_266])).
% 4.17/1.67  tff(c_272, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_30, c_268])).
% 4.17/1.67  tff(c_275, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_41), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_272])).
% 4.17/1.67  tff(c_277, plain, (![C_200]: (r2_hidden(C_200, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_200)) | ~v13_waybel_0('#skF_2'('#skF_5', '#skF_6', C_200), k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_200)) | ~r2_hidden(C_200, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_200, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_275])).
% 4.17/1.67  tff(c_281, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_277])).
% 4.17/1.67  tff(c_284, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_281])).
% 4.17/1.67  tff(c_285, plain, (![C_41]: (r2_hidden(C_41, '#skF_6') | ~r2_hidden('#skF_6', '#skF_2'('#skF_5', '#skF_6', C_41)) | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', C_41)) | ~r2_hidden(C_41, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_41, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_284])).
% 4.17/1.67  tff(c_342, plain, (![B_241]: (r2_hidden('#skF_4'('#skF_5', B_241), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_241))) | ~r2_hidden('#skF_4'('#skF_5', B_241), k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_241)) | v1_xboole_0('#skF_3'('#skF_5', B_241)) | ~m1_subset_1('#skF_4'('#skF_5', B_241), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_241, '#skF_5') | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_339, c_285])).
% 4.17/1.67  tff(c_348, plain, (![B_241]: (r2_hidden('#skF_4'('#skF_5', B_241), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_241))) | ~r2_hidden('#skF_4'('#skF_5', B_241), k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_241)) | v1_xboole_0('#skF_3'('#skF_5', B_241)) | ~m1_subset_1('#skF_4'('#skF_5', B_241), u1_struct_0('#skF_5')) | v4_pre_topc(B_241, '#skF_5') | ~m1_subset_1(B_241, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_342])).
% 4.17/1.67  tff(c_385, plain, (![B_248]: (r2_hidden('#skF_4'('#skF_5', B_248), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_248))) | ~r2_hidden('#skF_4'('#skF_5', B_248), k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_248)) | v1_xboole_0('#skF_3'('#skF_5', B_248)) | ~m1_subset_1('#skF_4'('#skF_5', B_248), u1_struct_0('#skF_5')) | v4_pre_topc(B_248, '#skF_5') | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_348])).
% 4.17/1.67  tff(c_389, plain, (![B_59]: (r2_hidden('#skF_4'('#skF_5', B_59), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_59)) | v1_xboole_0('#skF_3'('#skF_5', B_59)) | ~m1_subset_1('#skF_4'('#skF_5', B_59), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v4_pre_topc(B_59, '#skF_5') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_318, c_385])).
% 4.17/1.67  tff(c_392, plain, (![B_59]: (r2_hidden('#skF_4'('#skF_5', B_59), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_59)) | v1_xboole_0('#skF_3'('#skF_5', B_59)) | ~m1_subset_1('#skF_4'('#skF_5', B_59), u1_struct_0('#skF_5')) | v4_pre_topc(B_59, '#skF_5') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_389])).
% 4.17/1.67  tff(c_394, plain, (![B_249]: (r2_hidden('#skF_4'('#skF_5', B_249), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_249))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_249)) | v1_xboole_0('#skF_3'('#skF_5', B_249)) | ~m1_subset_1('#skF_4'('#skF_5', B_249), u1_struct_0('#skF_5')) | v4_pre_topc(B_249, '#skF_5') | ~m1_subset_1(B_249, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_392])).
% 4.17/1.67  tff(c_398, plain, (![B_59]: (r2_hidden('#skF_4'('#skF_5', B_59), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_59)) | v1_xboole_0('#skF_3'('#skF_5', B_59)) | v4_pre_topc(B_59, '#skF_5') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_40, c_394])).
% 4.17/1.67  tff(c_401, plain, (![B_59]: (r2_hidden('#skF_4'('#skF_5', B_59), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_59))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_59)) | v1_xboole_0('#skF_3'('#skF_5', B_59)) | v4_pre_topc(B_59, '#skF_5') | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_398])).
% 4.17/1.67  tff(c_403, plain, (![B_250]: (r2_hidden('#skF_4'('#skF_5', B_250), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', B_250))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', B_250)) | v1_xboole_0('#skF_3'('#skF_5', B_250)) | v4_pre_topc(B_250, '#skF_5') | ~m1_subset_1(B_250, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_401])).
% 4.17/1.67  tff(c_406, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | ~r2_hidden('#skF_6', '#skF_3'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_403])).
% 4.17/1.67  tff(c_409, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_3'('#skF_5', '#skF_6')) | v4_pre_topc('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_117, c_406])).
% 4.17/1.67  tff(c_410, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6') | v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_101, c_109, c_409])).
% 4.17/1.67  tff(c_411, plain, (v1_xboole_0('#skF_2'('#skF_5', '#skF_6', '#skF_4'('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_410])).
% 4.17/1.67  tff(c_32, plain, (![A_23, B_35, C_41]: (~v1_xboole_0('#skF_2'(A_23, B_35, C_41)) | ~r2_hidden(C_41, k2_pre_topc(A_23, B_35)) | ~m1_subset_1(C_41, u1_struct_0(A_23)) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23) | v2_struct_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_334, plain, (![A_230, B_232, B_231]: (~v1_xboole_0('#skF_2'(A_230, B_232, '#skF_4'(A_230, B_231))) | ~r2_hidden(B_232, '#skF_3'(A_230, B_231)) | v1_xboole_0('#skF_3'(A_230, B_231)) | ~m1_subset_1('#skF_4'(A_230, B_231), u1_struct_0(A_230)) | ~m1_subset_1(B_232, k1_zfmisc_1(u1_struct_0(A_230))) | v4_pre_topc(B_231, A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_320, c_32])).
% 4.17/1.67  tff(c_413, plain, (~r2_hidden('#skF_6', '#skF_3'('#skF_5', '#skF_6')) | v1_xboole_0('#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_411, c_334])).
% 4.17/1.67  tff(c_416, plain, (v1_xboole_0('#skF_3'('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5')) | v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_117, c_413])).
% 4.17/1.67  tff(c_417, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_109, c_416])).
% 4.17/1.67  tff(c_420, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_40, c_417])).
% 4.17/1.67  tff(c_423, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_420])).
% 4.17/1.67  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_423])).
% 4.17/1.67  tff(c_426, plain, (r2_hidden('#skF_4'('#skF_5', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_410])).
% 4.17/1.67  tff(c_36, plain, (![A_45, B_59]: (~r2_hidden('#skF_4'(A_45, B_59), B_59) | v4_pre_topc(B_59, A_45) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_45))) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_429, plain, (v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_426, c_36])).
% 4.17/1.67  tff(c_432, plain, (v4_pre_topc('#skF_6', '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_429])).
% 4.17/1.67  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_101, c_432])).
% 4.17/1.67  tff(c_436, plain, (v4_pre_topc('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 4.17/1.67  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_444, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_66])).
% 4.17/1.67  tff(c_68, plain, (r2_hidden('#skF_6', '#skF_7') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_438, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_68])).
% 4.17/1.67  tff(c_435, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 4.17/1.67  tff(c_76, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_450, plain, (v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_76])).
% 4.17/1.67  tff(c_74, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_446, plain, (v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_74])).
% 4.17/1.67  tff(c_72, plain, (v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_448, plain, (v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_72])).
% 4.17/1.67  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_452, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_436, c_70])).
% 4.17/1.67  tff(c_64, plain, (r2_waybel_7('#skF_5', '#skF_7', '#skF_8') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_442, plain, (r2_waybel_7('#skF_5', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_64])).
% 4.17/1.67  tff(c_567, plain, (![C_320, A_321, B_322, D_323]: (r2_hidden(C_320, k2_pre_topc(A_321, B_322)) | ~r2_waybel_7(A_321, D_323, C_320) | ~r2_hidden(B_322, D_323) | ~m1_subset_1(D_323, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_321))))) | ~v3_waybel_7(D_323, k3_yellow_1(k2_struct_0(A_321))) | ~v13_waybel_0(D_323, k3_yellow_1(k2_struct_0(A_321))) | ~v2_waybel_0(D_323, k3_yellow_1(k2_struct_0(A_321))) | v1_xboole_0(D_323) | ~m1_subset_1(C_320, u1_struct_0(A_321)) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0(A_321))) | ~l1_pre_topc(A_321) | ~v2_pre_topc(A_321) | v2_struct_0(A_321))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.17/1.67  tff(c_571, plain, (![B_322]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_322)) | ~r2_hidden(B_322, '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v3_waybel_7('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_7', k3_yellow_1(k2_struct_0('#skF_5'))) | v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_442, c_567])).
% 4.17/1.67  tff(c_578, plain, (![B_322]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_322)) | ~r2_hidden(B_322, '#skF_7') | v1_xboole_0('#skF_7') | ~m1_subset_1(B_322, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_444, c_450, c_446, c_448, c_452, c_571])).
% 4.17/1.67  tff(c_580, plain, (![B_324]: (r2_hidden('#skF_8', k2_pre_topc('#skF_5', B_324)) | ~r2_hidden(B_324, '#skF_7') | ~m1_subset_1(B_324, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_435, c_578])).
% 4.17/1.67  tff(c_583, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_54, c_580])).
% 4.17/1.67  tff(c_586, plain, (r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_438, c_583])).
% 4.17/1.67  tff(c_10, plain, (![A_1, B_13, C_19]: (v13_waybel_0('#skF_1'(A_1, B_13, C_19), k3_yellow_1(k2_struct_0(A_1))) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_12, plain, (![A_1, B_13, C_19]: (v2_waybel_0('#skF_1'(A_1, B_13, C_19), k3_yellow_1(k2_struct_0(A_1))) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_8, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_1))))) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_14, plain, (![A_1, B_13, C_19]: (v1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(k3_yellow_1(k2_struct_0(A_1)))) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_16, plain, (![A_1, B_13, C_19]: (~v1_xboole_0('#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_592, plain, (~v1_xboole_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_586, c_16])).
% 4.17/1.67  tff(c_605, plain, (~v1_xboole_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_444, c_592])).
% 4.17/1.67  tff(c_606, plain, (~v1_xboole_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_605])).
% 4.17/1.67  tff(c_62, plain, (~r2_hidden('#skF_8', '#skF_6') | ~v4_pre_topc('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.17/1.67  tff(c_440, plain, (~r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_62])).
% 4.17/1.67  tff(c_6, plain, (![B_13, A_1, C_19]: (r2_hidden(B_13, '#skF_1'(A_1, B_13, C_19)) | ~r2_hidden(C_19, k2_pre_topc(A_1, B_13)) | ~m1_subset_1(C_19, u1_struct_0(A_1)) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_pre_topc(A_1) | ~v2_pre_topc(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_588, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_586, c_6])).
% 4.17/1.67  tff(c_597, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_6', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_444, c_588])).
% 4.17/1.67  tff(c_598, plain, (r2_hidden('#skF_6', '#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_60, c_597])).
% 4.17/1.67  tff(c_495, plain, (![A_281, B_282, C_283]: (r1_waybel_7(A_281, '#skF_1'(A_281, B_282, C_283), C_283) | ~r2_hidden(C_283, k2_pre_topc(A_281, B_282)) | ~m1_subset_1(C_283, u1_struct_0(A_281)) | ~m1_subset_1(B_282, k1_zfmisc_1(u1_struct_0(A_281))) | ~l1_pre_topc(A_281) | ~v2_pre_topc(A_281) | v2_struct_0(A_281))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.67  tff(c_501, plain, (![C_283]: (r1_waybel_7('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_283), C_283) | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_54, c_495])).
% 4.17/1.67  tff(c_506, plain, (![C_283]: (r1_waybel_7('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_283), C_283) | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_501])).
% 4.17/1.67  tff(c_507, plain, (![C_283]: (r1_waybel_7('#skF_5', '#skF_1'('#skF_5', '#skF_6', C_283), C_283) | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_506])).
% 4.17/1.67  tff(c_622, plain, (![D_332, B_333, A_334, C_335]: (r2_hidden(D_332, B_333) | ~r1_waybel_7(A_334, C_335, D_332) | ~m1_subset_1(D_332, u1_struct_0(A_334)) | ~r2_hidden(B_333, C_335) | ~m1_subset_1(C_335, k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(A_334))))) | ~v13_waybel_0(C_335, k3_yellow_1(k2_struct_0(A_334))) | ~v2_waybel_0(C_335, k3_yellow_1(k2_struct_0(A_334))) | ~v1_subset_1(C_335, u1_struct_0(k3_yellow_1(k2_struct_0(A_334)))) | v1_xboole_0(C_335) | ~v4_pre_topc(B_333, A_334) | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0(A_334))) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334) | v2_struct_0(A_334))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.17/1.67  tff(c_624, plain, (![C_283, B_333]: (r2_hidden(C_283, B_333) | ~r2_hidden(B_333, '#skF_1'('#skF_5', '#skF_6', C_283)) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', C_283), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', C_283), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', C_283), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_1'('#skF_5', '#skF_6', C_283), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_1'('#skF_5', '#skF_6', C_283)) | ~v4_pre_topc(B_333, '#skF_5') | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_507, c_622])).
% 4.17/1.67  tff(c_629, plain, (![C_283, B_333]: (r2_hidden(C_283, B_333) | ~r2_hidden(B_333, '#skF_1'('#skF_5', '#skF_6', C_283)) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', C_283), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', C_283), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', C_283), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_1'('#skF_5', '#skF_6', C_283), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_1'('#skF_5', '#skF_6', C_283)) | ~v4_pre_topc(B_333, '#skF_5') | ~m1_subset_1(B_333, k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5') | ~r2_hidden(C_283, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_283, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_624])).
% 4.17/1.67  tff(c_697, plain, (![C_380, B_381]: (r2_hidden(C_380, B_381) | ~r2_hidden(B_381, '#skF_1'('#skF_5', '#skF_6', C_380)) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', C_380), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', C_380), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', C_380), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_1'('#skF_5', '#skF_6', C_380), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_1'('#skF_5', '#skF_6', C_380)) | ~v4_pre_topc(B_381, '#skF_5') | ~m1_subset_1(B_381, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden(C_380, k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1(C_380, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_60, c_629])).
% 4.17/1.67  tff(c_699, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_1'('#skF_5', '#skF_6', '#skF_8')) | ~v4_pre_topc('#skF_6', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_598, c_697])).
% 4.17/1.67  tff(c_702, plain, (r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))) | v1_xboole_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_586, c_54, c_436, c_699])).
% 4.17/1.67  tff(c_703, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_606, c_440, c_702])).
% 4.17/1.67  tff(c_704, plain, (~v1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5'))))), inference(splitLeft, [status(thm)], [c_703])).
% 4.17/1.67  tff(c_707, plain, (~r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_14, c_704])).
% 4.17/1.67  tff(c_710, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_444, c_586, c_707])).
% 4.17/1.67  tff(c_712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_710])).
% 4.17/1.67  tff(c_713, plain, (~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(splitRight, [status(thm)], [c_703])).
% 4.17/1.67  tff(c_715, plain, (~m1_subset_1('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0('#skF_5')))))), inference(splitLeft, [status(thm)], [c_713])).
% 4.17/1.67  tff(c_718, plain, (~r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_8, c_715])).
% 4.17/1.67  tff(c_721, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_444, c_586, c_718])).
% 4.17/1.67  tff(c_723, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_721])).
% 4.17/1.67  tff(c_724, plain, (~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5'))) | ~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_713])).
% 4.17/1.67  tff(c_749, plain, (~v2_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_724])).
% 4.17/1.67  tff(c_752, plain, (~r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_12, c_749])).
% 4.17/1.67  tff(c_755, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_444, c_586, c_752])).
% 4.17/1.67  tff(c_757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_755])).
% 4.17/1.67  tff(c_758, plain, (~v13_waybel_0('#skF_1'('#skF_5', '#skF_6', '#skF_8'), k3_yellow_1(k2_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_724])).
% 4.17/1.67  tff(c_762, plain, (~r2_hidden('#skF_8', k2_pre_topc('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_10, c_758])).
% 4.17/1.67  tff(c_765, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_444, c_586, c_762])).
% 4.17/1.67  tff(c_767, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_765])).
% 4.17/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.17/1.67  
% 4.17/1.67  Inference rules
% 4.17/1.67  ----------------------
% 4.17/1.67  #Ref     : 0
% 4.17/1.67  #Sup     : 116
% 4.17/1.67  #Fact    : 0
% 4.17/1.67  #Define  : 0
% 4.17/1.67  #Split   : 8
% 4.17/1.67  #Chain   : 0
% 4.17/1.67  #Close   : 0
% 4.17/1.67  
% 4.17/1.67  Ordering : KBO
% 4.17/1.67  
% 4.17/1.67  Simplification rules
% 4.17/1.67  ----------------------
% 4.17/1.67  #Subsume      : 39
% 4.17/1.67  #Demod        : 145
% 4.17/1.67  #Tautology    : 21
% 4.17/1.67  #SimpNegUnit  : 42
% 4.17/1.67  #BackRed      : 0
% 4.17/1.67  
% 4.17/1.67  #Partial instantiations: 0
% 4.17/1.67  #Strategies tried      : 1
% 4.17/1.67  
% 4.17/1.67  Timing (in seconds)
% 4.17/1.67  ----------------------
% 4.17/1.68  Preprocessing        : 0.35
% 4.17/1.68  Parsing              : 0.18
% 4.17/1.68  CNF conversion       : 0.03
% 4.17/1.68  Main loop            : 0.55
% 4.17/1.68  Inferencing          : 0.23
% 4.17/1.68  Reduction            : 0.16
% 4.17/1.68  Demodulation         : 0.11
% 4.17/1.68  BG Simplification    : 0.03
% 4.17/1.68  Subsumption          : 0.11
% 4.17/1.68  Abstraction          : 0.02
% 4.17/1.68  MUC search           : 0.00
% 4.17/1.68  Cooper               : 0.00
% 4.17/1.68  Total                : 0.98
% 4.17/1.68  Index Insertion      : 0.00
% 4.17/1.68  Index Deletion       : 0.00
% 4.17/1.68  Index Matching       : 0.00
% 4.17/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
